#include <errno.h>
#include <sstream>
#include <string>
#include <glog/logging.h>
#include <rados/librados.hpp>
#include "zlog.pb.h"
#include "libzlog.h"

/*
 * Pack a protobuf message into a bufferlist.
 */
template<typename T>
void pack_msg(ceph::bufferlist& bl, T& m) {
  CHECK(m.IsInitialized());
  char buf[m.ByteSize()];
  CHECK(m.SerializeToArray(buf, sizeof(buf)));
  bl.append(buf, sizeof(buf));
}

/*
 * Unpack a protobuf message from a bufferlist.
 */
template<typename T>
bool unpack_msg(T& m, ceph::bufferlist& bl) {
  if (!m.ParseFromArray(bl.c_str(), bl.length())) {
    LOG(ERROR) << "unpack_msg: could not parse message";
    return false;
  }
  if (!m.IsInitialized()) {
    LOG(ERROR) << "unpack_msg: message is uninitialized";
    return false;
  }
  return true;
}

static std::string metalog_oid_from_name(const std::string& name)
{
  std::stringstream ss;
  ss << name << ".meta";
  return ss.str();
}

namespace zlog {

int Log::Create(librados::IoCtx& ioctx, const std::string& name,
    int stripe_size, Log **log)
{
  if (stripe_size <= 0) {
    LOG(ERROR) << "Invalid stripe size (" << stripe_size << " <= 0)";
    return -EINVAL;
  }

  if (name.length() == 0) {
    LOG(ERROR) << "Invalid log name (empty string)";
    return -EINVAL;
  }

  // pack up config info in a buffer
  zlog::MetaLog config;
  config.set_stripe_size(stripe_size);
  ceph::bufferlist bl;
  pack_msg<zlog::MetaLog>(bl, config);

  // setup rados operation to create log
  librados::ObjectWriteOperation op;
  op.create(true); // exclusive create
  op.write_full(bl);

  std::string metalog_oid = metalog_oid_from_name(name);
  int ret = ioctx.operate(metalog_oid, &op);
  if (ret) {
    LOG(ERROR) << "Failed to create log " << name << " ret "
      << ret << " (" << strerror(-ret) << ")";
    return ret;
  }

  Log *new_log = new Log();

  new_log->ioctx_ = &ioctx;
  new_log->name_ = name;
  new_log->metalog_oid_ = metalog_oid;
  new_log->stripe_size_ = stripe_size;

  *log = new_log;

  return 0;
}

}
