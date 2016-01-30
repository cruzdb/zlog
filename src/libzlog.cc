#include <cerrno>
#include <iostream>
#include <sstream>
#include <string>
#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>
#include "libzlog.hpp"
#include "zlog.pb.h"
#include "protobuf_bufferlist_adapter.h"
#include "internal.hpp"

/*
 * We can use Ceph API to query and make some intelligent decisiosn about what
 * the stripe size should be at runtime. In any case logs are not created
 * programmatically where this is needed. They are created for instance with a
 * CLI tool, and in any case the width can be changed online.
 */
#define DEFAULT_STRIPE_SIZE 100

namespace zlog {

std::string LogLL::metalog_oid_from_name(const std::string& name)
{
  std::stringstream ss;
  ss << name << ".meta";
  return ss.str();
}

std::string LogLL::position_to_oid(uint64_t position)
{
  // round-robin striping
  int slot = position % stripe_size_;
  return slot_to_oid(slot);
}

std::string LogLL::slot_to_oid(int slot)
{
  std::stringstream ss;
  ss << name_ << "." << slot;
  return ss.str();
}

int LogLL::Create(librados::IoCtx& ioctx, const std::string& name,
    int stripe_size, SeqrClient *seqr, LogLL& log)
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
  cls_zlog_set_projection(op, 0, bl);

  std::string metalog_oid = LogLL::metalog_oid_from_name(name);
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
  log.seqr = seqr;

  ret = log.RefreshProjection();
  if (ret)
    return ret;

  return 0;
}

int LogLL::Open(librados::IoCtx& ioctx, const std::string& name,
    SeqrClient *seqr, LogLL& log)
{
  if (name.length() == 0) {
    std::cerr << "Invalid log name (empty string)" << std::endl;
    return -EINVAL;
  }

  /*
   * Check that the log metadata/head object exists. The projection and other
   * state is read during RefreshProjection.
   */
  std::string metalog_oid = LogLL::metalog_oid_from_name(name);
  int ret = ioctx.stat(metalog_oid, NULL, NULL);
  if (ret) {
    std::cerr << "Failed to open log meta object " << metalog_oid << " ret " <<
      ret << std::endl;
    return ret;
  }

  log.ioctx_ = &ioctx;
  log.pool_ = ioctx.get_pool_name();
  log.name_ = name;
  log.metalog_oid_ = metalog_oid;
  log.seqr = seqr;

  ret = log.RefreshProjection();
  if (ret)
    return ret;

  return 0;
}

int LogLL::CreateCut(uint64_t *pepoch, uint64_t *maxpos)
{
  /*
   * Get the current projection. We'll make a copy of this as the next
   * projection.
   */
  int rv;
  uint64_t epoch;
  ceph::bufferlist bl;
  librados::ObjectReadOperation get_op;
  cls_zlog_get_latest_projection(get_op, &rv, &epoch, &bl);

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

  zlog_proto::MetaLog config;
  if (!unpack_msg<zlog_proto::MetaLog>(config, bl)) {
    std::cerr << "failed to parse configuration" << std::endl;
    return -EIO;
  }

  /*
   * Seal the current epoch/projection.
   */
  for (int i = 0; i < config.stripe_size(); i++) {
    std::string oid = slot_to_oid(i);
    librados::ObjectWriteOperation seal_op;
    cls_zlog_seal(seal_op, epoch);
    ret = ioctx_->operate(oid, &seal_op);
    if (ret != zlog::CLS_ZLOG_OK) {
      std::cerr << "failed to seal object" << std::endl;
      return ret;
    }
  }

  /*
   * Calculate the max log position.
   */
  uint64_t max_position;
  ret = FindMaxPosition(epoch, config.stripe_size(), &max_position);
  if (ret) {
    std::cerr << "failed to find max pos ret " << ret << std::endl;
    return ret;
  }

  /*
   * Propose the next epoch / projection.
   */
  uint64_t next_epoch = epoch + 1;
  librados::ObjectWriteOperation set_op;
  cls_zlog_set_projection(set_op, next_epoch, bl);
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

int LogLL::Seal(uint64_t epoch)
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

int LogLL::FindMaxPosition(uint64_t epoch, int ss, uint64_t *pposition)
{
  uint64_t max_position;
  bool first = true;

  assert(ss > 0);

  for (int i = 0; i < ss; i++) {
    std::string oid = slot_to_oid(i);

    /*
     * Prepare max_position operation
     */
    int op_ret;
    uint64_t this_pos;
    librados::ObjectReadOperation op;
    cls_zlog_max_position(op, epoch, &this_pos, &op_ret);

    /*
     * The max_position function should only be called on objects that have
     * been sealed, thus here we return from any error includes -ENOENT. The
     * epoch tag must also match the sealed epoch in the object otherwise
     * we'll receive -EINVAL.
     */
    ceph::bufferlist unused;
    int ret = ioctx_->operate(oid, &op, &unused);
    if (ret != zlog::CLS_ZLOG_OK) {
      std::cerr << "failed to find max pos ret " << ret << std::endl;
      return ret;
    }

    if (op_ret != zlog::CLS_ZLOG_OK) {
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

  *pposition =  max_position;

  return 0;
}

int LogLL::RefreshProjection()
{
  for (;;) {
    int rv;
    uint64_t epoch;
    ceph::bufferlist bl;
    librados::ObjectReadOperation op;
    cls_zlog_get_latest_projection(op, &rv, &epoch, &bl);

    ceph::bufferlist unused;
    int ret = ioctx_->operate(metalog_oid_, &op, &unused);
    if (ret || rv) {
      std::cerr << "failed to get projection ret "
        << ret << " rv " << rv << std::endl;
      sleep(1);
      continue;
    }

    zlog_proto::MetaLog config;
    if (!unpack_msg<zlog_proto::MetaLog>(config, bl)) {
      std::cerr << "failed to parse configuration" << std::endl;
      return -EIO;
    }

    epoch_ = epoch;
    stripe_size_ = config.stripe_size();
    break;
  }

  return 0;
}

int LogLL::CheckTail(uint64_t *pposition, bool increment)
{
  for (;;) {
    int ret = seqr->CheckTail(epoch_, pool_, name_, pposition, increment);
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

int LogLL::CheckTail(std::vector<uint64_t>& positions, size_t count)
{
  if (count <= 0 || count > 100)
    return -EINVAL;

  for (;;) {
    std::vector<uint64_t> result;
    int ret = seqr->CheckTail(epoch_, pool_, name_, result, count);
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

int LogLL::CheckTail(const std::set<uint64_t>& stream_ids,
    std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
    uint64_t *pposition, bool increment)
{
  for (;;) {
    int ret = seqr->CheckTail(epoch_, pool_, name_, stream_ids,
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
 * client try again with the same position?
 *
 * 2. When a stale epoch return code occurs we continuously look for a new
 * projection and retry the append. to avoid just spinning and creating holes
 * we pause for a second. other options include waiting to observe an _actual_
 * change to a new projection. that is probably better...
 */
int LogLL::Append(ceph::bufferlist& data, uint64_t *pposition)
{
  for (;;) {
    uint64_t position;
    int ret = CheckTail(&position, true);
    if (ret)
      return ret;

    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, epoch_, position, data);

    std::string oid = position_to_oid(position);
    ret = ioctx_->operate(oid, &op);
    if (ret < 0) {
      std::cerr << "append: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == zlog::CLS_ZLOG_OK) {
      if (pposition)
        *pposition = position;
      return 0;
    }

    if (ret == zlog::CLS_ZLOG_STALE_EPOCH) {
      sleep(1); // avoid spinning in this loop
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(ret == zlog::CLS_ZLOG_READ_ONLY);
  }
  assert(0);
}

int LogLL::Fill(uint64_t epoch, uint64_t position)
{
  for (;;) {
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, epoch, position);

    std::string oid = position_to_oid(position);
    int ret = ioctx_->operate(oid, &op);
    if (ret < 0) {
      std::cerr << "fill: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == zlog::CLS_ZLOG_OK)
      return 0;

    if (ret == zlog::CLS_ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(ret == zlog::CLS_ZLOG_READ_ONLY);
    return -EROFS;
  }
}

int LogLL::Fill(uint64_t position)
{
  for (;;) {
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, epoch_, position);

    std::string oid = position_to_oid(position);
    int ret = ioctx_->operate(oid, &op);
    if (ret < 0) {
      std::cerr << "fill: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == zlog::CLS_ZLOG_OK)
      return 0;

    if (ret == zlog::CLS_ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(ret == zlog::CLS_ZLOG_READ_ONLY);
    return -EROFS;
  }
}

int LogLL::Trim(uint64_t position)
{
  for (;;) {
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_trim(op, epoch_, position);

    std::string oid = position_to_oid(position);
    int ret = ioctx_->operate(oid, &op);
    if (ret < 0) {
      std::cerr << "trim: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == zlog::CLS_ZLOG_OK)
      return 0;

    if (ret == zlog::CLS_ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(0);
  }
}

int LogLL::Read(uint64_t epoch, uint64_t position, ceph::bufferlist& bl)
{
  for (;;) {
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, epoch, position);

    std::string oid = position_to_oid(position);
    int ret = ioctx_->operate(oid, &op, &bl);
    if (ret < 0) {
      std::cerr << "read failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == zlog::CLS_ZLOG_OK)
      return 0;
    else if (ret == zlog::CLS_ZLOG_NOT_WRITTEN)
      return -ENODEV;
    else if (ret == zlog::CLS_ZLOG_INVALIDATED)
      return -EFAULT;
    else if (ret == zlog::CLS_ZLOG_STALE_EPOCH) {
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

int LogLL::Read(uint64_t position, ceph::bufferlist& bl)
{
  for (;;) {
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, epoch_, position);

    std::string oid = position_to_oid(position);
    int ret = ioctx_->operate(oid, &op, &bl);
    if (ret < 0) {
      std::cerr << "read failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == zlog::CLS_ZLOG_OK)
      return 0;
    else if (ret == zlog::CLS_ZLOG_NOT_WRITTEN)
      return -ENODEV;
    else if (ret == zlog::CLS_ZLOG_INVALIDATED)
      return -EFAULT;
    else if (ret == zlog::CLS_ZLOG_STALE_EPOCH) {
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

  int ret = zlog::LogLL::Open(ctx->ioctx, name,
      ctx->seqr, ctx->log);
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

  int ret = zlog::LogLL::Create(ctx->ioctx, name, DEFAULT_STRIPE_SIZE,
      ctx->seqr, ctx->log);
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

  int ret = zlog::LogLL::OpenOrCreate(ctx->ioctx, name, DEFAULT_STRIPE_SIZE,
      ctx->seqr, ctx->log);
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
  return ctx->log.CheckTail(pposition);
}

extern "C" int zlog_append(zlog_log_t log, const void *data, size_t len,
    uint64_t *pposition)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  ceph::bufferlist bl;
  bl.append((char*)data, len);
  return ctx->log.Append(bl, pposition);
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
  return ctx->log.MultiAppend(bl, ids, pposition);
}

extern "C" int zlog_read(zlog_log_t log, uint64_t position, void *data,
    size_t len)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  ceph::bufferlist bl;
  ceph::bufferptr bp = ceph::buffer::create_static(len, (char*)data);
  bl.push_back(bp);
  int ret = ctx->log.Read(position, bl);
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
  return ctx->log.Fill(position);
}

extern "C" int zlog_trim(zlog_log_t log, uint64_t position)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  return ctx->log.Trim(position);
}

/*
 * If nothing goes into this except LogLL then we should just remove this
 * level of indirection and point directly to LogLL.
 */
class LogHL::LogHLImpl {
 public:
  LogLL log;
};

/*
 * FIXME: switch to return pointer and add destructor
 */
int LogHL::Create(librados::IoCtx& ioctx, const std::string& name,
    SeqrClient *seqr, LogHL **logptr)
{
  LogHL *log = new LogHL;
  log->impl = new LogHLImpl;

  int ret = LogLL::Create(ioctx, name, DEFAULT_STRIPE_SIZE, seqr, log->impl->log);
  if (ret) {
    delete log->impl;
    delete log;
    return ret;
  }

  *logptr = log;

  return 0;
}

int LogHL::Open(librados::IoCtx& ioctx, const std::string& name,
    SeqrClient *seqr, LogHL **logptr)
{
  LogHL *log = new LogHL;
  log->impl = new LogHLImpl;

  int ret = LogLL::Open(ioctx, name, seqr, log->impl->log);
  if (ret) {
    delete log->impl;
    delete log;
    return ret;
  }

  *logptr = log;

  return 0;
}

int LogHL::Append(ceph::bufferlist& data, uint64_t *pposition)
{
  return impl->log.Append(data, pposition);
}

int LogHL::Read(uint64_t position, ceph::bufferlist& bl)
{
  return impl->log.Read(position, bl);
}

int LogHL::Fill(uint64_t position)
{
  return impl->log.Fill(position);
}

int LogHL::CheckTail(uint64_t *pposition)
{
  return impl->log.CheckTail(pposition);
}

int LogHL::Trim(uint64_t position)
{
  return impl->log.Trim(position);
}

struct LogHL::AioCompletionImpl {
  LogLL::AioCompletion *c;
};

LogHL::AioCompletion *LogHL::aio_create_completion(void *arg,
    zlog::LogHL::AioCompletion::callback_t cb)
{
  LogHL::AioCompletionImpl *impl = new LogHL::AioCompletionImpl;
  impl->c = LogLL::aio_create_completion(arg, cb);
  return new AioCompletion(impl);
}

LogHL::AioCompletion *LogHL::aio_create_completion()
{
  return aio_create_completion(NULL, NULL);
}

int LogHL::AioCompletion::get_return_value()
{
  LogHL::AioCompletionImpl *impl = (LogHL::AioCompletionImpl*)pc;
  return impl->c->get_return_value();
}

void LogHL::AioCompletion::set_callback(void *arg,
    zlog::LogHL::AioCompletion::callback_t cb)
{
  LogHL::AioCompletionImpl *impl = (LogHL::AioCompletionImpl*)pc;
  impl->c->set_callback(arg, cb);
}

void LogHL::AioCompletion::wait_for_complete()
{
  LogHL::AioCompletionImpl *impl = (LogHL::AioCompletionImpl*)pc;
  impl->c->wait_for_complete();
}

void LogHL::AioCompletion::release()
{
  LogHL::AioCompletionImpl *impl = (LogHL::AioCompletionImpl*)pc;
  impl->c->release();
  delete this;
}

int LogHL::AioAppend(AioCompletion *c, ceph::bufferlist& data, uint64_t *pposition)
{
  LogHL::AioCompletionImpl *cimpl = (LogHL::AioCompletionImpl*)c->pc;
  return impl->log.AioAppend(cimpl->c, data, pposition);
}

int LogHL::AioRead(uint64_t position, AioCompletion *c, ceph::bufferlist *bpl)
{
  LogHL::AioCompletionImpl *cimpl = (LogHL::AioCompletionImpl*)c->pc;
  return impl->log.AioRead(position, cimpl->c, bpl);
}

/*
 * If we don't stash anything in here except a LogLL then we should just
 * remove it and point directly to the LogLL
 */
class LogHL::Stream::StreamImpl {
 public:
  LogLL::Stream stream;
};

/*
 * FIXME: Memory leak on StreamImpl
 */
int LogHL::OpenStream(uint64_t stream_id, Stream **streamptr)
{
  LogHL::Stream *stream = new LogHL::Stream;
  stream->impl = new LogHL::Stream::StreamImpl;

  int ret = impl->log.OpenStream(stream_id, stream->impl->stream);
  if (ret) {
    delete stream->impl;
    delete stream;
  }

  *streamptr = stream;

  return 0;
}

int LogHL::Stream::Append(ceph::bufferlist& data, uint64_t *pposition)
{
  return impl->stream.Append(data, pposition);
}

int LogHL::Stream::ReadNext(ceph::bufferlist& bl, uint64_t *pposition)
{
  return impl->stream.ReadNext(bl, pposition);
}

int LogHL::Stream::Reset()
{
  return impl->stream.Reset();
}

int LogHL::Stream::Sync()
{
  return impl->stream.Sync();
}

uint64_t LogHL::Stream::Id() const
{
  return impl->stream.Id();
}

std::vector<uint64_t> LogHL::Stream::History() const
{
  return impl->stream.History();
}

int LogHL::MultiAppend(ceph::bufferlist& data,
    const std::set<uint64_t>& stream_ids, uint64_t *pposition)
{
  return impl->log.MultiAppend(data, stream_ids, pposition);
}

int LogHL::StreamMembership(std::set<uint64_t>& stream_ids, uint64_t position)
{
  return impl->log.StreamMembership(stream_ids, position);
}

}
