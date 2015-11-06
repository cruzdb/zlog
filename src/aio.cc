#include <mutex>
#include <condition_variable>
#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>
#include "libzlog.hpp"

namespace zlog {

enum AioType {
  ZLOG_AIO_APPEND,
  ZLOG_AIO_READ,
};

struct zlog::Log::AioCompletionImpl {
  std::condition_variable cond;
  std::mutex lock;
  int ref;
  bool complete;
  bool released;

  /*
   * Common
   *
   * position:
   *   - current attempt (append)
   *   - target (read)
   * bl:
   *  - data being appended (append)
   *  - temp storage for read (read)
   */
  int retval;
  Log::AioCompletion::callback_t safe_cb;
  void *safe_cb_arg;
  uint64_t position;
  ceph::bufferlist bl;
  AioType type;

  /*
   * AioAppend
   *
   * pposition:
   *  - final append position
   */
  uint64_t *pposition;

  /*
   * AioRead
   *
   * pbl:
   *  - where to put result
   */
  ceph::bufferlist *pbl;

  Log *log;
  librados::IoCtx *ioctx;
  librados::AioCompletion *c;

  AioCompletionImpl() :
    ref(1), complete(false), released(false), retval(0)
  {}

  int wait_for_complete() {
    std::unique_lock<std::mutex> l(lock);
    cond.wait(l, [&]{ return complete; });
    return 0;
  }

  int get_return_value() {
    std::lock_guard<std::mutex> l(lock);
    return retval;
  }

  void release() {
    lock.lock();
    assert(!released);
    released = true;
    put_unlock();
  }

  void put_unlock() {
    assert(ref > 0);
    int n = --ref;
    lock.unlock();
    if (!n)
      delete this;
  }

  void get() {
    std::lock_guard<std::mutex> l(lock);
    assert(ref > 0);
    ref++;
  }

  void set_callback(void *arg, zlog::Log::AioCompletion::callback_t cb) {
    std::lock_guard<std::mutex> l(lock);
    safe_cb = cb;
    safe_cb_arg = arg;
  }

  static void aio_safe_cb(librados::completion_t cb, void *arg);
};

void zlog::Log::AioCompletion::wait_for_complete()
{
  AioCompletionImpl *impl = (AioCompletionImpl*)pc;
  impl->wait_for_complete();
}

int zlog::Log::AioCompletion::get_return_value()
{
  zlog::Log::AioCompletionImpl *impl = (AioCompletionImpl*)pc;
  return impl->get_return_value();
}

void zlog::Log::AioCompletion::release()
{
  zlog::Log::AioCompletionImpl *impl = (AioCompletionImpl*)pc;
  impl->release();
  delete this;
}

void zlog::Log::AioCompletion::set_callback(void *arg,
    zlog::Log::AioCompletion::callback_t cb)
{
  zlog::Log::AioCompletionImpl *impl = (AioCompletionImpl*)pc;
  impl->set_callback(arg, cb);
}

/*
 *
 */
void zlog::Log::AioCompletionImpl::aio_safe_cb(librados::completion_t cb, void *arg)
{
  zlog::Log::AioCompletionImpl *impl = (zlog::Log::AioCompletionImpl*)arg;
  librados::AioCompletion *rc = impl->c;
  bool finish = false;

  impl->lock.lock();

  int ret = rc->get_return_value();

  // done with the rados completion
  rc->release();

  assert(impl->type == ZLOG_AIO_APPEND ||
         impl->type == ZLOG_AIO_READ);

  if (ret == zlog::CLS_ZLOG_OK) {
    /*
     * Append was successful. We're done.
     */
    if (impl->type == ZLOG_AIO_APPEND && impl->pposition) {
      *impl->pposition = impl->position;
    } else if (impl->type == ZLOG_AIO_READ && impl->pbl &&
        impl->bl.length() > 0) {
      *impl->pbl = impl->bl;
    }
    ret = 0;
    finish = true;
  } else if (ret == zlog::CLS_ZLOG_STALE_EPOCH) {
    /*
     * We'll need to try again with a new epoch.
     */
    ret = impl->log->RefreshProjection();
    if (ret)
      finish = true;
  } else if (ret < 0) {
    /*
     * Encountered a RADOS error.
     */
    finish = true;
  } else if (ret == zlog::CLS_ZLOG_NOT_WRITTEN) {
    assert(impl->type == ZLOG_AIO_READ);
    ret = -ENODEV;
    finish = true;
  } else if (ret == zlog::CLS_ZLOG_INVALIDATED) {
    assert(impl->type == ZLOG_AIO_READ);
    ret = -EFAULT;
    finish = true;
  } else {
    if (impl->type == ZLOG_AIO_APPEND)
      assert(ret == zlog::CLS_ZLOG_READ_ONLY);
    else
      assert(0);
  }

  /*
   * Try append again with a new position. This can happen if above there is a
   * stale epoch that we refresh, or if the position was marked read-only.
   */
  if (!finish) {
    if (impl->type == ZLOG_AIO_APPEND) {
      // if we are appending, get a new position
      uint64_t position;
      ret = impl->log->CheckTail(&position, true);
      if (ret)
        finish = true;
      else
        impl->position = position;
    }

    // we are still good. build a new aio
    if (!finish) {
      impl->c = librados::Rados::aio_create_completion(impl, NULL, aio_safe_cb);
      assert(impl->c);
      // don't need impl->get(): reuse reference

      // build and submit new op
      std::string oid = impl->log->position_to_oid(impl->position);
      switch (impl->type) {
        case ZLOG_AIO_APPEND:
          {
            librados::ObjectWriteOperation op;
            zlog::cls_zlog_write(op, impl->log->epoch_, impl->position, impl->bl);
            ret = impl->ioctx->aio_operate(oid, impl->c, &op);
            if (ret)
              finish = true;
          }
          break;

        case ZLOG_AIO_READ:
          {
            librados::ObjectReadOperation op;
            zlog::cls_zlog_read(op, impl->log->epoch_, impl->position);
            ret = impl->ioctx->aio_operate(oid, impl->c, &op, &impl->bl);
            if (ret)
              finish = true;
          }
          break;

        default:
          assert(0);
      }
    }
  }

  // complete aio if append success, or any error
  if (finish) {
    impl->retval = ret;
    impl->complete = true;
    impl->lock.unlock();
    if (impl->safe_cb)
      impl->safe_cb(impl, impl->safe_cb_arg);
    impl->cond.notify_all();
    impl->lock.lock();
    impl->put_unlock();
    return;
  }

  impl->lock.unlock();
}

Log::AioCompletion *Log::aio_create_completion(void *arg,
    Log::AioCompletion::callback_t cb)
{
  AioCompletionImpl *impl = new AioCompletionImpl;
  impl->safe_cb = cb;
  impl->safe_cb_arg = arg;
  return new AioCompletion(impl);
}

Log::AioCompletion *Log::aio_create_completion()
{
  return aio_create_completion(NULL, NULL);
}

/*
 * The retry for AioAppend is coordinated through the aio_safe_cb callback
 * which will dispatch a new rados operation.
 */
int Log::AioAppend(AioCompletion *c, ceph::bufferlist& data,
    uint64_t *pposition)
{
  // initial position guess
  uint64_t position;
  int ret = CheckTail(&position, true);
  if (ret)
    return ret;

  AioCompletionImpl *impl = (AioCompletionImpl*)c->pc;

  impl->log = this;
  impl->bl = data;
  impl->position = position;
  impl->pposition = pposition;
  impl->ioctx = ioctx_;
  impl->type = ZLOG_AIO_APPEND;

  impl->get(); // rados aio now has a reference
  impl->c = librados::Rados::aio_create_completion(impl, NULL,
      AioCompletionImpl::aio_safe_cb);
  assert(impl->c);

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_write(op, epoch_, position, data);

  std::string oid = position_to_oid(position);
  ret = ioctx_->aio_operate(oid, impl->c, &op);
  /*
   * Currently aio_operate never fails. If in the future that changes then we
   * need to make sure that references to impl and the rados completion are
   * cleaned up correctly.
   */
  assert(ret == 0);

  return ret;
}

int Log::AioRead(uint64_t position, AioCompletion *c,
    ceph::bufferlist *pbl)
{
  AioCompletionImpl *impl = (AioCompletionImpl*)c->pc;

  impl->log = this;
  impl->pbl = pbl;
  impl->position = position;
  impl->ioctx = ioctx_;
  impl->type = ZLOG_AIO_READ;

  impl->get(); // rados aio now has a reference
  impl->c = librados::Rados::aio_create_completion(impl, NULL,
      AioCompletionImpl::aio_safe_cb);
  assert(impl->c);

  librados::ObjectReadOperation op;
  zlog::cls_zlog_read(op, epoch_, position);

  std::string oid = position_to_oid(position);
  int ret = ioctx_->aio_operate(oid, impl->c, &op, &impl->bl);
  /*
   * Currently aio_operate never fails. If in the future that changes then we
   * need to make sure that references to impl and the rados completion are
   * cleaned up correctly.
   */
  assert(ret == 0);

  return ret;
}

}
