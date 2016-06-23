#include "log_impl.h"

#include <cerrno>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include <rados/librados.hpp>

#include "proto/zlog.pb.h"
#include "proto/protobuf_bufferlist_adapter.h"
#include "include/zlog/log.h"
#include "include/zlog/capi.h"

#include "stripe_history.h"
#include "backend.h"

/*
 * We can use Ceph API to query and make some intelligent decisiosn about what
 * the stripe size should be at runtime. In any case logs are not created
 * programmatically where this is needed. They are created for instance with a
 * CLI tool, and in any case the width can be changed online.
 */
#define DEFAULT_STRIPE_SIZE 100

namespace zlog {

std::string LogImpl::metalog_oid_from_name(const std::string& name)
{
  std::stringstream ss;
  ss << name << ".meta";
  return ss.str();
}

int Log::CreateWithStripeWidth(librados::IoCtx& ioctx, const std::string& name,
    SeqrClient *seqr, int stripe_size, Log **logptr)
{
  if (stripe_size <= 0) {
    std::cerr << "Invalid stripe size (" << stripe_size << " <= 0)" << std::endl;
    return -EINVAL;
  }

  if (name.length() == 0) {
    std::cerr << "Invalid log name (empty string)" << std::endl;
    return -EINVAL;
  }

  // Setup the first projection
  StripeHistory hist;
  hist.AddStripe(0, 0, stripe_size);
  ceph::bufferlist bl = hist.Serialize();

  /*
   * Create the log metadata/head object and create the first projection. The
   * initial projection number is epoch = 0. Note that we don't initially seal
   * the objects that the log will be striped across. The semantics of
   * cls_zlog are such that unitialized objects behave exactly as if they had
   * been sealed with epoch = -1.
   *
   * The projection will be initialized for this log object during
   * RefreshProjection in the same way that it is done during Open().
   */
  librados::ObjectWriteOperation op;
  op.create(true); // exclusive create
  Backend::set_projection(op, 0, bl);

  std::string metalog_oid = LogImpl::metalog_oid_from_name(name);
  int ret = ioctx.operate(metalog_oid, &op);
  if (ret) {
    std::cerr << "Failed to create log " << name << " ret "
      << ret << " (" << strerror(-ret) << ")" << std::endl;
    return ret;
  }

  LogImpl *impl = new LogImpl;

  impl->ioctx_ = &ioctx;
  impl->pool_ = ioctx.get_pool_name();
  impl->name_ = name;
  impl->metalog_oid_ = metalog_oid;
  impl->seqr = seqr;
  impl->mapper_.SetName(name);

  // default backend. this can be changed using LogImpl::set_backend_vN
  // interface immediately after this call and before any log I/O occurs. It
  // is up to the client to make sure that the correct version is used and
  // that no version mixing occurs.
  impl->backend = Backend::CreateV1();

  ret = impl->RefreshProjection();
  if (ret) {
    delete impl;
    return ret;
  }

  *logptr = impl;

  return 0;
}

int Log::Create(librados::IoCtx& ioctx, const std::string& name,
    SeqrClient *seqr, Log **logptr)
{
  return CreateWithStripeWidth(ioctx, name, seqr, DEFAULT_STRIPE_SIZE, logptr);
}

int Log::Open(librados::IoCtx& ioctx, const std::string& name,
    SeqrClient *seqr, Log **logptr)
{
  if (name.length() == 0) {
    std::cerr << "Invalid log name (empty string)" << std::endl;
    return -EINVAL;
  }

  /*
   * Check that the log metadata/head object exists. The projection and other
   * state is read during RefreshProjection.
   */
  std::string metalog_oid = LogImpl::metalog_oid_from_name(name);
  int ret = ioctx.stat(metalog_oid, NULL, NULL);
  if (ret) {
    std::cerr << "Failed to open log meta object " << metalog_oid << " ret " <<
      ret << std::endl;
    return ret;
  }

  LogImpl *impl = new LogImpl;

  impl->ioctx_ = &ioctx;
  impl->pool_ = ioctx.get_pool_name();
  impl->name_ = name;
  impl->metalog_oid_ = metalog_oid;
  impl->seqr = seqr;
  impl->mapper_.SetName(name);

  // default backend. this can be changed using LogImpl::set_backend_vN
  // interface immediately after this call and before any log I/O occurs. It
  // is up to the client to make sure that the correct version is used and
  // that no version mixing occurs.
  impl->backend = Backend::CreateV1();

  ret = impl->RefreshProjection();
  if (ret) {
    delete impl;
    return ret;
  }

  *logptr = impl;

  return 0;
}

int LogImpl::StripeWidth()
{
  return mapper_.CurrentStripeWidth();
}

/*
 * Create a new stripe empty stripe.
 *
 * TODO:
 *   CreateNewStripe, CreateCut, SetStripeWidth are all nearly identical
 *   methods that could be unified.
 */
int LogImpl::CreateNewStripe()
{
  assert(backend_ver == 2);

  /*
   * Get the current projection. We'll add the new striping width when we
   * propose the next projection/epoch.
   */
  int rv;
  uint64_t epoch;
  ceph::bufferlist in_bl;
  librados::ObjectReadOperation get_op;
  Backend::get_latest_projection(get_op, &rv, &epoch, &in_bl);

  ceph::bufferlist unused;
  int ret = ioctx_->operate(metalog_oid_, &get_op, &unused);
  if (ret || rv) {
    std::cerr << "failed to get projection ret " << ret
      << " rv " << rv << std::endl;
    if (ret)
      return ret;
    if (rv)
      return rv;
  }

  StripeHistory hist;
  ret = hist.Deserialize(in_bl);
  if (ret)
    return ret;
  assert(!hist.Empty());

  std::vector<std::string> objects;
  mapper_.LatestObjectSet(objects, hist);

  uint64_t max_position;
  ret = Seal(objects, epoch, &max_position);
  if (ret) {
    std::cerr << "failed to seal " << ret << std::endl;
    return ret;
  }

  /*
   * When we create a new empty stripe we have sealed the previous stripe and
   * gotten the max_position for that stripe. However, if no writes occurred
   * to the new stripe then max_position will be zero.
   */
  uint64_t next_epoch = epoch + 1;
  hist.CloneLatestStripe(max_position, next_epoch);
  ceph::bufferlist out_bl = hist.Serialize();

  /*
   * Propose the updated projection for the next epoch.
   */
  librados::ObjectWriteOperation set_op;
  Backend::set_projection(set_op, next_epoch, out_bl);
  ret = ioctx_->operate(metalog_oid_, &set_op);
  if (ret) {
    std::cerr << "failed to set new epoch " << next_epoch
      << " ret " << ret << std::endl;
    return ret;
  }

  return 0;
}

int LogImpl::SetStripeWidth(int width)
{
  /*
   * Get the current projection. We'll add the new striping width when we
   * propose the next projection/epoch.
   */
  int rv;
  uint64_t epoch;
  ceph::bufferlist in_bl;
  librados::ObjectReadOperation get_op;
  Backend::get_latest_projection(get_op, &rv, &epoch, &in_bl);

  ceph::bufferlist unused;
  int ret = ioctx_->operate(metalog_oid_, &get_op, &unused);
  if (ret || rv) {
    std::cerr << "failed to get projection ret " << ret
      << " rv " << rv << std::endl;
    if (ret)
      return ret;
    if (rv)
      return rv;
  }

  StripeHistory hist;
  ret = hist.Deserialize(in_bl);
  if (ret)
    return ret;
  assert(!hist.Empty());

  std::vector<std::string> objects;
  mapper_.LatestObjectSet(objects, hist);

  uint64_t max_position;
  ret = Seal(objects, epoch, &max_position);
  if (ret) {
    std::cerr << "failed to seal " << ret << std::endl;
    return ret;
  }

  uint64_t next_epoch = epoch + 1;
  hist.AddStripe(max_position, next_epoch, width);
  ceph::bufferlist out_bl = hist.Serialize();

  /*
   * Propose the updated projection for the next epoch.
   */
  librados::ObjectWriteOperation set_op;
  Backend::set_projection(set_op, next_epoch, out_bl);
  ret = ioctx_->operate(metalog_oid_, &set_op);
  if (ret) {
    std::cerr << "failed to set new epoch " << next_epoch
      << " ret " << ret << std::endl;
    return ret;
  }

  return 0;
}

int LogImpl::CreateCut(uint64_t *pepoch, uint64_t *maxpos)
{
  /*
   * Get the current projection. We'll make a copy of this as the next
   * projection.
   */
  int rv;
  uint64_t epoch;
  ceph::bufferlist bl;
  librados::ObjectReadOperation get_op;
  Backend::get_latest_projection(get_op, &rv, &epoch, &bl);

  ceph::bufferlist unused;
  int ret = ioctx_->operate(metalog_oid_, &get_op, &unused);
  if (ret || rv) {
    std::cerr << "failed to get projection ret " << ret
      << " rv " << rv << std::endl;
    if (ret)
      return ret;
    if (rv)
      return rv;
  }

  StripeHistory hist;
  ret = hist.Deserialize(bl);
  if (ret)
    return ret;
  assert(!hist.Empty());

  std::vector<std::string> objects;
  mapper_.LatestObjectSet(objects, hist);

  uint64_t max_position;
  ret = Seal(objects, epoch, &max_position);
  if (ret) {
    std::cerr << "failed to seal " << ret << std::endl;
    return ret;
  }

  /*
   * Propose the next epoch / projection.
   */
  uint64_t next_epoch = epoch + 1;
  librados::ObjectWriteOperation set_op;
  Backend::set_projection(set_op, next_epoch, bl);
  ret = ioctx_->operate(metalog_oid_, &set_op);
  if (ret) {
    std::cerr << "failed to set new epoch " << next_epoch
      << " ret " << ret << std::endl;
    return ret;
  }

  *pepoch = next_epoch;
  *maxpos = max_position;

  return 0;
}

int LogImpl::Seal(const std::vector<std::string>& objects,
    uint64_t epoch, uint64_t *next_pos)
{
  /*
   * Seal each object
   */
  for (const auto& oid : objects) {
    librados::ObjectWriteOperation seal_op;
    backend->seal(seal_op, epoch);
    int ret = ioctx_->operate(oid, &seal_op);
    if (ret != Backend::CLS_ZLOG_OK) {
      std::cerr << "failed to seal object" << std::endl;
      return ret;
    }
  }

  /*
   * Get next position from each object
   */
  uint64_t max_position;
  bool first = true;
  for (const auto& oid : objects) {
    /*
     * Prepare max_position operation
     */
    int op_ret;
    uint64_t this_pos;
    librados::ObjectReadOperation op;
    backend->max_position(op, epoch, &this_pos, &op_ret);

    /*
     * The max_position function should only be called on objects that have
     * been sealed, thus here we return from any error includes -ENOENT. The
     * epoch tag must also match the sealed epoch in the object otherwise
     * we'll receive -EINVAL.
     */
    ceph::bufferlist unused;
    int ret = ioctx_->operate(oid, &op, &unused);
    if (ret != Backend::CLS_ZLOG_OK) {
      std::cerr << "failed to find max pos ret " << ret << std::endl;
      return ret;
    }

    if (op_ret != Backend::CLS_ZLOG_OK) {
      std::cerr << "failed to find max pos op_ret " << ret << std::endl;
      return ret;
    }

    if (first) {
      max_position = this_pos;
      first = false;
      continue;
    }

    max_position = std::max(max_position, this_pos);
  }

  *next_pos = max_position;

  return 0;
}

int LogImpl::RefreshProjection()
{
  for (;;) {
    int rv;
    uint64_t epoch;
    ceph::bufferlist bl;
    librados::ObjectReadOperation op;
    Backend::get_latest_projection(op, &rv, &epoch, &bl);

    ceph::bufferlist unused;
    int ret = ioctx_->operate(metalog_oid_, &op, &unused);
    if (ret || rv) {
      std::cerr << "failed to get projection ret "
        << ret << " rv " << rv << std::endl;
      sleep(1);
      continue;
    }

    StripeHistory hist;
    ret = hist.Deserialize(bl);
    if (ret)
      return ret;
    assert(!hist.Empty());

    mapper_.SetHistory(hist, epoch);

    break;
  }

  return 0;
}

int LogImpl::CheckTail(uint64_t *pposition, bool increment)
{
  for (;;) {
    int ret = seqr->CheckTail(mapper_.Epoch(), pool_, name_, pposition, increment);
    if (ret == -EAGAIN) {
      //std::cerr << "check tail ret -EAGAIN" << std::endl;
      sleep(1);
      continue;
    } else if (ret == -ERANGE) {
      //std::cerr << "check tail ret -ERANGE" << std::endl;
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }
    return ret;
  }
  assert(0);
}

int LogImpl::CheckTail(uint64_t *pposition)
{
  return CheckTail(pposition, false);
}

int LogImpl::CheckTail(std::vector<uint64_t>& positions, size_t count)
{
  if (count <= 0 || count > 100)
    return -EINVAL;

  for (;;) {
    std::vector<uint64_t> result;
    int ret = seqr->CheckTail(mapper_.Epoch(), pool_, name_, result, count);
    if (ret == -EAGAIN) {
      //std::cerr << "check tail ret -EAGAIN" << std::endl;
      sleep(1);
      continue;
    } else if (ret == -ERANGE) {
      //std::cerr << "check tail ret -ERANGE" << std::endl;
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }
    if (ret == 0)
      positions.swap(result);
    return ret;
  }
  assert(0);
}

int LogImpl::CheckTail(const std::set<uint64_t>& stream_ids,
    std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
    uint64_t *pposition, bool increment)
{
  for (;;) {
    int ret = seqr->CheckTail(mapper_.Epoch(), pool_, name_, stream_ids,
        stream_backpointers, pposition, increment);
    if (ret == -EAGAIN) {
      //std::cerr << "check tail ret -EAGAIN" << std::endl;
      sleep(1);
      continue;
    } else if (ret == -ERANGE) {
      //std::cerr << "check tail ret -ERANGE" << std::endl;
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }
    return ret;
  }
  assert(0);
}

/*
 * TODO:
 *
 * 1. When a stale epoch is encountered the projection is refreshed and the
 * append is retried with a new tail position retrieved from the sequencer.
 * This means that a hole is created each time an append hits a stale epoch.
 * If there are a lot of clients, a large hole is created each time the
 * projection is refreshed. Is this necessary in all cases? When could a
 * client try again with the same position? We could also mitigate this affect
 * a bit by having the sequencer, upon startup, begin finding log tails
 * proactively instead of waiting for a client to perform a check tail.
 *
 * 2. When a stale epoch return code occurs we continuously look for a new
 * projection and retry the append. to avoid just spinning and creating holes
 * we pause for a second. other options include waiting to observe an _actual_
 * change to a new projection. that is probably better...
 */
int LogImpl::Append(ceph::bufferlist& data, uint64_t *pposition)
{
  for (;;) {
    uint64_t position;
    int ret = CheckTail(&position, true);
    if (ret)
      return ret;

    uint64_t epoch;
    std::string oid;
    mapper_.FindObject(position, &oid, &epoch);

    librados::ObjectWriteOperation op;
    backend->write(op, epoch, position, data);

    ret = ioctx_->operate(oid, &op);
    if (ret < 0 && ret != -EFBIG) {
      std::cerr << "append: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == Backend::CLS_ZLOG_OK) {
      if (pposition)
        *pposition = position;
      return 0;
    }

    if (ret == Backend::CLS_ZLOG_STALE_EPOCH) {
      sleep(1); // avoid spinning in this loop
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    /*
     * When an object becomes too large we seal the entire stripe and create a
     * new stripe of empty objects. First we refresh the projection and try
     * the append again if the projection changed. Otherwise we will attempt
     * to create the new stripe.
     */
    if (ret == -EFBIG) {
      assert(backend_ver == 2);
      CreateNewStripe();
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(ret == Backend::CLS_ZLOG_READ_ONLY);
  }
  assert(0);
}

int LogImpl::Fill(uint64_t epoch, uint64_t position)
{
  for (;;) {
    librados::ObjectWriteOperation op;
    backend->fill(op, epoch, position);

    std::string oid;
    mapper_.FindObject(position, &oid, NULL);

    int ret = ioctx_->operate(oid, &op);
    if (ret < 0) {
      std::cerr << "fill: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == Backend::CLS_ZLOG_OK)
      return 0;

    if (ret == Backend::CLS_ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(ret == Backend::CLS_ZLOG_READ_ONLY);
    return -EROFS;
  }
}

int LogImpl::Fill(uint64_t position)
{
  for (;;) {
    uint64_t epoch;
    std::string oid;
    mapper_.FindObject(position, &oid, &epoch);

    librados::ObjectWriteOperation op;
    backend->fill(op, epoch, position);

    int ret = ioctx_->operate(oid, &op);
    if (ret < 0) {
      std::cerr << "fill: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == Backend::CLS_ZLOG_OK)
      return 0;

    if (ret == Backend::CLS_ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(ret == Backend::CLS_ZLOG_READ_ONLY);
    return -EROFS;
  }
}

int LogImpl::Trim(uint64_t position)
{
  for (;;) {
    uint64_t epoch;
    std::string oid;
    mapper_.FindObject(position, &oid, &epoch);

    librados::ObjectWriteOperation op;
    backend->trim(op, epoch, position);

    int ret = ioctx_->operate(oid, &op);
    if (ret < 0) {
      std::cerr << "trim: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == Backend::CLS_ZLOG_OK)
      return 0;

    if (ret == Backend::CLS_ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(0);
  }
}

int LogImpl::Read(uint64_t epoch, uint64_t position, ceph::bufferlist& bl)
{
  for (;;) {
    librados::ObjectReadOperation op;
    backend->read(op, epoch, position);

    std::string oid;
    mapper_.FindObject(position, &oid, NULL);

    int ret = ioctx_->operate(oid, &op, &bl);
    if (ret < 0) {
      std::cerr << "read failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == Backend::CLS_ZLOG_OK)
      return 0;
    else if (ret == Backend::CLS_ZLOG_NOT_WRITTEN)
      return -ENODEV;
    else if (ret == Backend::CLS_ZLOG_INVALIDATED)
      return -EFAULT;
    else if (ret == Backend::CLS_ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    } else {
      std::cerr << "unknown reply";
      assert(0);
    }
  }
  assert(0);
}

int LogImpl::Read(uint64_t position, ceph::bufferlist& bl)
{
  for (;;) {
    uint64_t epoch;
    std::string oid;
    mapper_.FindObject(position, &oid, &epoch);

    librados::ObjectReadOperation op;
    backend->read(op, epoch, position);

    int ret = ioctx_->operate(oid, &op, &bl);
    if (ret < 0) {
      std::cerr << "read failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == Backend::CLS_ZLOG_OK)
      return 0;
    else if (ret == Backend::CLS_ZLOG_NOT_WRITTEN)
      return -ENODEV;
    else if (ret == Backend::CLS_ZLOG_INVALIDATED)
      return -EFAULT;
    else if (ret == Backend::CLS_ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    } else {
      std::cerr << "unknown reply";
      assert(0);
    }
  }
  assert(0);
}

extern "C" int zlog_destroy(zlog_log_t log)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  delete ctx->log;
  delete ctx->seqr;
  delete ctx;
  return 0;
}

extern "C" int zlog_open(rados_ioctx_t ioctx, const char *name,
    const char *host, const char *port,
    zlog_log_t *log)
{
  zlog_log_ctx *ctx = new zlog_log_ctx;

  librados::IoCtx::from_rados_ioctx_t(ioctx, ctx->ioctx);

  ctx->seqr = new zlog::SeqrClient(host, port);
  ctx->seqr->Connect();

  int ret = zlog::Log::Open(ctx->ioctx, name,
      ctx->seqr, &ctx->log);
  if (ret) {
    delete ctx->seqr;
    delete ctx;
    return ret;
  }

  *log = ctx;

  return 0;
}

extern "C" int zlog_create(rados_ioctx_t ioctx, const char *name,
    const char *host, const char *port, zlog_log_t *log)
{
  zlog_log_ctx *ctx = new zlog_log_ctx;

  librados::IoCtx::from_rados_ioctx_t(ioctx, ctx->ioctx);

  ctx->seqr = new zlog::SeqrClient(host, port);
  ctx->seqr->Connect();

  int ret = zlog::Log::Create(ctx->ioctx, name,
      ctx->seqr, &ctx->log);
  if (ret) {
    delete ctx->seqr;
    delete ctx;
    return ret;
  }

  *log = ctx;

  return 0;
}

extern "C" int zlog_open_or_create(rados_ioctx_t ioctx, const char *name,
    const char *host, const char *port, zlog_log_t *log)
{
  zlog_log_ctx *ctx = new zlog_log_ctx;

  librados::IoCtx::from_rados_ioctx_t(ioctx, ctx->ioctx);

  ctx->seqr = new zlog::SeqrClient(host, port);
  ctx->seqr->Connect();

  int ret = zlog::Log::OpenOrCreate(ctx->ioctx, name,
      ctx->seqr, &ctx->log);
  if (ret) {
    delete ctx->seqr;
    delete ctx;
    return ret;
  }

  *log = ctx;

  return 0;
}

extern "C" int zlog_checktail(zlog_log_t log, uint64_t *pposition)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  return ctx->log->CheckTail(pposition);
}

extern "C" int zlog_append(zlog_log_t log, const void *data, size_t len,
    uint64_t *pposition)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  ceph::bufferlist bl;
  bl.append((char*)data, len);
  return ctx->log->Append(bl, pposition);
}

extern "C" int zlog_multiappend(zlog_log_t log, const void *data,
    size_t data_len, const uint64_t *stream_ids, size_t stream_ids_len,
    uint64_t *pposition)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  if (stream_ids_len == 0)
    return -EINVAL;
  std::set<uint64_t> ids(stream_ids, stream_ids + stream_ids_len);
  ceph::bufferlist bl;
  bl.append((char*)data, data_len);
  return ctx->log->MultiAppend(bl, ids, pposition);
}

extern "C" int zlog_read(zlog_log_t log, uint64_t position, void *data,
    size_t len)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  ceph::bufferlist bl;
  ceph::bufferptr bp = ceph::buffer::create_static(len, (char*)data);
  bl.push_back(bp);
  int ret = ctx->log->Read(position, bl);
  if (ret >= 0) {
    if (bl.length() > len)
      return -ERANGE;
    if (bl.c_str() != data)
      bl.copy(0, bl.length(), (char*)data);
    ret = bl.length();
  }
  return ret;
}

extern "C" int zlog_fill(zlog_log_t log, uint64_t position)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  return ctx->log->Fill(position);
}

extern "C" int zlog_trim(zlog_log_t log, uint64_t position)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  return ctx->log->Trim(position);
}

}
