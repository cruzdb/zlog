#include "zlog/backend/ceph.h"
#include "cls_zlog_client.h"

CephBackend::CephBackend(librados::IoCtx *ioctx) :
  ioctx_(ioctx)
{
  pool_ = ioctx_->get_pool_name();
}

struct AioContext {
  librados::AioCompletion *c;
  void *arg;
  std::function<void(void*, int)> cb;
  ceph::bufferlist bl;
  std::string *data;
};

void CephBackend::aio_safe_cb_append(librados::completion_t cb, void *arg)
{
  AioContext *c = (AioContext*)arg;
  librados::AioCompletion *rc = c->c;
  int ret = rc->get_return_value();
  rc->release();
  c->cb(c->arg, zlog_rv(ret));
  delete c;
}

int CephBackend::AioAppend(const std::string& oid, uint64_t epoch,
    uint64_t position, const Slice& data, void *arg,
    std::function<void(void*, int)> callback)
{
  AioContext *c = new AioContext;
  c->arg = arg;
  c->cb = callback;
  c->data = NULL;
  c->c = librados::Rados::aio_create_completion(c,
      NULL, CephBackend::aio_safe_cb_append);
  assert(c->c);

  ceph::bufferlist data_bl;
  data_bl.append(data.data(), data.size());

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_write(op, epoch, position, data_bl);

  int ret = ioctx_->aio_operate(oid, c->c, &op);
  assert(ret == 0);

  return ZLOG_OK;
}

void CephBackend::aio_safe_cb_read(librados::completion_t cb, void *arg)
{
  AioContext *c = (AioContext*)arg;
  librados::AioCompletion *rc = c->c;
  int ret = rc->get_return_value();
  rc->release();
  if (ret == zlog::CLS_ZLOG_OK && c->bl.length() > 0)
    c->data->assign(c->bl.c_str(), c->bl.length());
  c->cb(c->arg, zlog_rv(ret));
  delete c;
}

int CephBackend::AioRead(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data, void *arg,
    std::function<void(void*, int)> callback)
{
  AioContext *c = new AioContext;
  c->arg = arg;
  c->cb = callback;
  c->data = data;
  c->c = librados::Rados::aio_create_completion(c,
      NULL, CephBackend::aio_safe_cb_read);
  assert(c->c);

  librados::ObjectReadOperation op;
  zlog::cls_zlog_read(op, epoch, position);

  int ret = ioctx_->aio_operate(oid, c->c, &op, &c->bl);
  assert(ret == 0);

  return ZLOG_OK;
}

std::string CephBackend::pool()
{
  return pool_;
}

int CephBackend::Exists(const std::string& oid)
{
  int ret = ioctx_->stat(oid, NULL, NULL);
  return zlog_rv(ret);
}

int CephBackend::CreateHeadObject(const std::string& oid,
                     const zlog_proto::MetaLog& data)
{
  // prepare blob
  ceph::bufferlist bl;
  pack_msg<zlog_proto::MetaLog>(bl, data);

  // prepare operation
  librados::ObjectWriteOperation op;
  op.create(true); // exclusive create
  zlog::cls_zlog_set_projection(op, 0, bl);

  // run operation
  int ret = ioctx_->operate(oid, &op);
  return zlog_rv(ret);
}

int CephBackend::SetProjection(const std::string& oid, uint64_t epoch,
                  const zlog_proto::MetaLog& data)
{
  // prepare blob
  ceph::bufferlist bl;
  pack_msg<zlog_proto::MetaLog>(bl, data);

  // prepare operation
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_set_projection(op, epoch, bl);

  // run operation
  int ret = ioctx_->operate(oid, &op);
  return zlog_rv(ret);
}

int CephBackend::LatestProjection(const std::string& oid,
                     uint64_t *epoch, zlog_proto::MetaLog& config)
{
  // prepare operation
  int rv;
  ceph::bufferlist bl;
  librados::ObjectReadOperation op;
  zlog::cls_zlog_get_latest_projection(op, &rv, epoch, &bl);

  // run operation
  ceph::bufferlist unused;
  int ret = ioctx_->operate(oid, &op, &unused);
  if (ret || rv) {
    std::cerr << "LatestProjection: rv " << rv
              << " ret " << ret << std::endl;
    if (ret)
      return zlog_rv(ret);
    if (rv)
      return zlog_rv(rv);
  }

  // copy out data
  if (!unpack_msg<zlog_proto::MetaLog>(config, bl)) {
    std::cerr << "failed to parse configuration" << std::endl;
    return -EIO;
  }

  return zlog_rv(0);
}

int CephBackend::Seal(const std::string& oid, uint64_t epoch)
{
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_seal(op, epoch);
  int ret = ioctx_->operate(oid, &op);
  return zlog_rv(ret);
}

int CephBackend::MaxPos(const std::string& oid, uint64_t epoch,
           uint64_t *pos)
{
  // prepare operation
  int rv;
  librados::ObjectReadOperation op;
  zlog::cls_zlog_max_position(op, epoch, pos, &rv);

  // run operation
  ceph::bufferlist unused;
  int ret = ioctx_->operate(oid, &op, &unused);
  if (ret || rv) {
    std::cerr << "MaxPos ret " << ret << " rv " << rv << std::endl;
    if (ret)
      return zlog_rv(ret);
    if (rv)
      return zlog_rv(rv);
  }

  return zlog_rv(0);
}

int CephBackend::Write(const std::string& oid, const Slice& data,
          uint64_t epoch, uint64_t position)
{
  // prepare operation
  ceph::bufferlist data_bl;
  data_bl.append(data.data(), data.size());
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_write(op, epoch, position, data_bl);

  // run operation
  int ret = ioctx_->operate(oid, &op);
  return zlog_rv(ret);
}

int CephBackend::Read(const std::string& oid, uint64_t epoch,
                      uint64_t position, std::string *data)
{
  // prepare operation
  librados::ObjectReadOperation op;
  zlog::cls_zlog_read(op, epoch, position);

  // run operation
  ceph::bufferlist bl;
  int ret = ioctx_->operate(oid, &op, &bl);

  // success: copy data out
  if (ret == zlog::CLS_ZLOG_OK)
    data->assign(bl.c_str(), bl.length());

  return zlog_rv(ret);
}


int CephBackend::Trim(const std::string& oid, uint64_t epoch,
                      uint64_t position)
{
  // prepare operation
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_trim(op, epoch, position);

  // run operation
  int ret = ioctx_->operate(oid, &op);
  return zlog_rv(ret);
}

int CephBackend::Fill(const std::string& oid, uint64_t epoch,
    uint64_t position)
{
  // prepare operation
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_fill(op, epoch, position);

  // run operation
  int ret = ioctx_->operate(oid, &op);
  return zlog_rv(ret);
}

int CephBackend::zlog_rv(int ret)
{
  if (ret < 0)
    return ret;

  switch (ret) {
    case zlog::CLS_ZLOG_OK:
      return Backend::ZLOG_OK;

    case zlog::CLS_ZLOG_STALE_EPOCH:
      return Backend::ZLOG_STALE_EPOCH;

    case zlog::CLS_ZLOG_READ_ONLY:
      return Backend::ZLOG_READ_ONLY;

    case zlog::CLS_ZLOG_NOT_WRITTEN:
      return Backend::ZLOG_NOT_WRITTEN;

    case zlog::CLS_ZLOG_INVALIDATED:
      return Backend::ZLOG_INVALIDATED;

    case zlog::CLS_ZLOG_INVALID_EPOCH:
      return Backend::ZLOG_INVALID_EPOCH;

    default:
      assert(0);
      return -EIO;
  }
}
