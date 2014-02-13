#include <errno.h>
#include <sstream>
#include <string>
#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>
#include "libzlog.h"
#include "zlog.pb.h"

/*
 * Pack a protobuf message into a bufferlist.
 */
template<typename T>
void pack_msg(ceph::bufferlist& bl, T& m) {
  assert(m.IsInitialized());
  char buf[m.ByteSize()];
  assert(m.SerializeToArray(buf, sizeof(buf)));
  bl.append(buf, sizeof(buf));
}

/*
 * Unpack a protobuf message from a bufferlist.
 */
template<typename T>
bool unpack_msg(T& m, ceph::bufferlist& bl) {
  if (!m.ParseFromArray(bl.c_str(), bl.length())) {
    std::cerr << "unpack_msg: could not parse message" << std::endl;
    return false;
  }
  if (!m.IsInitialized()) {
    std::cerr << "unpack_msg: message is uninitialized" << std::endl;
    return false;
  }
  return true;
}

namespace zlog {

std::string Log::metalog_oid_from_name(const std::string& name)
{
  std::stringstream ss;
  ss << name << ".meta";
  return ss.str();
}

std::string Log::slot_to_oid(int slot)
{
  std::stringstream ss;
  ss << name_ << "." << slot;
  return ss.str();
}

int Log::Create(librados::IoCtx& ioctx, const std::string& name,
    int stripe_size, SeqrClient *seqr, Log& log)
{
  if (stripe_size <= 0) {
    std::cerr << "Invalid stripe size (" << stripe_size << " <= 0)" << std::endl;
    return -EINVAL;
  }

  if (name.length() == 0) {
    std::cerr << "Invalid log name (empty string)" << std::endl;
    return -EINVAL;
  }

  // pack up config info in a buffer
  zlog_proto::MetaLog config;
  config.set_stripe_size(stripe_size);
  ceph::bufferlist bl;
  pack_msg<zlog_proto::MetaLog>(bl, config);

  // setup rados operation to create log
  librados::ObjectWriteOperation op;
  op.create(true); // exclusive create
  op.write_full(bl);
  cls_zlog_set_projection(op);

  std::string metalog_oid = Log::metalog_oid_from_name(name);
  int ret = ioctx.operate(metalog_oid, &op);
  if (ret) {
    std::cerr << "Failed to create log " << name << " ret "
      << ret << " (" << strerror(-ret) << ")" << std::endl;
    return ret;
  }

  log.ioctx_ = &ioctx;
  log.pool_ = ioctx.get_pool_name();
  log.name_ = name;
  log.metalog_oid_ = metalog_oid;
  log.stripe_size_ = stripe_size;
  log.seqr = seqr;

  ret = log.RefreshProjection();
  if (ret)
    return ret;

  return 0;
}

int Log::Open(librados::IoCtx& ioctx, const std::string& name,
    SeqrClient *seqr, Log& log)
{
  if (name.length() == 0) {
    std::cerr << "Invalid log name (empty string)" << std::endl;
    return -EINVAL;
  }

  std::string metalog_oid = Log::metalog_oid_from_name(name);

  ceph::bufferlist bl;
  int ret = ioctx.read(metalog_oid, bl, 0, 0);
  if (ret < 0) {
    std::cerr << "failed to read object " << metalog_oid << " ret "
      << ret << std::endl;
    return ret;
  }

  zlog_proto::MetaLog config;
  if (!unpack_msg<zlog_proto::MetaLog>(config, bl)) {
    std::cerr << "failed to parse configuration" << std::endl;
    return -EIO;
  }

  log.ioctx_ = &ioctx;
  log.pool_ = ioctx.get_pool_name();
  log.name_ = name;
  log.metalog_oid_ = metalog_oid;
  log.stripe_size_ = config.stripe_size();
  log.seqr = seqr;

  ret = log.RefreshProjection();
  if (ret)
    return ret;

  return 0;
}

int Log::SetProjection(uint64_t *pepoch)
{
  librados::ObjectWriteOperation op;
  cls_zlog_set_projection(op);
  int ret = ioctx_->operate(metalog_oid_, &op);
  if (ret) {
    std::cerr << "failed to set projection " << ret << std::endl;
    return ret;
  }
  return GetProjection(pepoch);
}

int Log::GetProjection(uint64_t *pepoch)
{
  return cls_zlog_get_projection(*ioctx_, metalog_oid_, pepoch);
}

int Log::Seal(uint64_t epoch)
{
  for (int i = 0; i < stripe_size_; i++) {
    std::string oid = slot_to_oid(i);
    librados::ObjectWriteOperation op;
    cls_zlog_seal(op, epoch);
    int ret = ioctx_->operate(oid, &op);
    if (ret != zlog::CLS_ZLOG_OK) {
      std::cerr << "failed to seal object" << std::endl;
      return ret;
    }
  }
  return 0;
}

int Log::FindMaxPosition(uint64_t epoch, uint64_t *pposition)
{
  uint64_t max_position = 0;

  for (int i = 0; i < stripe_size_; i++) {
    std::string oid = slot_to_oid(i);

    librados::bufferlist bl;
    librados::ObjectReadOperation op;
    int op_ret;
    uint64_t this_pos;

    cls_zlog_max_position(op, epoch, &this_pos, &op_ret);

    int ret = ioctx_->operate(oid, &op, &bl);
    if (ret < 0) {
      if (ret == -ENOENT) // no writes yet
        continue;
      std::cerr << "failed to find max pos " << ret << std::endl;
      return ret;
    }

    if (op_ret == zlog::CLS_ZLOG_OK)
      max_position = std::max(max_position, this_pos);
  }

  *pposition =  max_position;

  return 0;
}

int Log::RefreshProjection()
{
  for (;;) {
    uint64_t epoch;
    int ret = GetProjection(&epoch);
    if (ret) {
      std::cerr << "failed to get projection ret " << ret << std::endl;
      sleep(1);
      continue;
    }
    epoch_ = epoch;
    break;
  }
  return 0;
}

int Log::CheckTail(uint64_t *pposition, bool increment)
{
  for (;;) {
    int ret = seqr->CheckTail(epoch_, pool_, name_, pposition, increment);
    if (ret == -EAGAIN) {
      std::cerr << "check tail ret -EAGAIN" << std::endl;
      sleep(1);
      continue;
    } else if (ret == -ERANGE) {
      std::cerr << "check tail ret -ERANGE" << std::endl;
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }
    return ret;
  }
  assert(0);
}

}
