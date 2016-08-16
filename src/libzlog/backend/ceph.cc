#include "zlog/backend/ceph.h"

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
