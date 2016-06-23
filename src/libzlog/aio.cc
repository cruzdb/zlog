#include "log_impl.h"

#include <condition_variable>
#include <mutex>
#include <rados/librados.hpp>
#include "backend.h"

namespace zlog {

enum AioType {
  ZLOG_AIO_APPEND,
  ZLOG_AIO_READ,
};

class AioCompletionImpl {
 public:
  /*
   * concurrency control
   */
  std::condition_variable cond;
  std::mutex lock;
  int ref;
  bool complete;
  bool released;

  /*
   * base log and rados completion
   */
  LogImpl *log;
  librados::IoCtx *ioctx;
  librados::AioCompletion *c;

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
  bool has_callback;
  std::function<void()> callback;
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
  uint64_t epoch;

  /*
   * AioRead
   *
   * pbl:
   *  - where to put result
   */
  ceph::bufferlist *pbl;

  AioCompletionImpl() :
    ref(1), complete(false), released(false), retval(0)
  {}

  void WaitForComplete() {
    std::unique_lock<std::mutex> l(lock);
    cond.wait(l, [&]{ return complete; });
  }

  int ReturnValue() {
    std::lock_guard<std::mutex> l(lock);
    return retval;
  }

  void Release() {
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

  void SetCallback(std::function<void()> callback) {
    std::lock_guard<std::mutex> l(lock);
    has_callback = true;
    this->callback = callback;
  }

  static void aio_safe_cb_read(librados::completion_t cb, void *arg);
  static void aio_safe_cb_append(librados::completion_t cb, void *arg);
};

/*
 *
 */
void AioCompletionImpl::aio_safe_cb_read(librados::completion_t cb, void *arg)
{
  AioCompletionImpl *impl = (AioCompletionImpl*)arg;
  librados::AioCompletion *rc = impl->c;
  bool finish = false;

  impl->lock.lock();

  int ret = rc->get_return_value();

  // done with the rados completion
  rc->release();

  assert(impl->type == ZLOG_AIO_READ);

  if (ret == Backend::CLS_ZLOG_OK) {
    /*
     * Read was successful. We're done.
     */
    if (impl->pbl && impl->bl.length() > 0) {
      *impl->pbl = impl->bl;
    }
    ret = 0;
    finish = true;
  } else if (ret == Backend::CLS_ZLOG_STALE_EPOCH) {
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
  } else if (ret == Backend::CLS_ZLOG_NOT_WRITTEN) {
    ret = -ENODEV;
    finish = true;
  } else if (ret == Backend::CLS_ZLOG_INVALIDATED) {
    ret = -EFAULT;
    finish = true;
  } else {
    assert(0);
  }

  /*
   * Try append again with a new position. This can happen if above there is a
   * stale epoch that we refresh, or if the position was marked read-only.
   */
  if (!finish) {
    impl->c = librados::Rados::aio_create_completion(impl, NULL, aio_safe_cb_read);
    assert(impl->c);
    // don't need impl->get(): reuse reference

    uint64_t epoch;
    std::string oid;
    impl->log->mapper_.FindObject(impl->position, &oid, &epoch);

    // build and submit new op
    librados::ObjectReadOperation op;
    impl->log->backend->read(op, epoch, impl->position);
    ret = impl->ioctx->aio_operate(oid, impl->c, &op, &impl->bl);
    if (ret)
      finish = true;
  }

  // complete aio if append success, or any error
  if (finish) {
    impl->retval = ret;
    impl->complete = true;
    impl->lock.unlock();
    if (impl->has_callback)
      impl->callback();
    impl->cond.notify_all();
    impl->lock.lock();
    impl->put_unlock();
    return;
  }

  impl->lock.unlock();
}

/*
 *
 */
void AioCompletionImpl::aio_safe_cb_append(librados::completion_t cb, void *arg)
{
  AioCompletionImpl *impl = (AioCompletionImpl*)arg;
  librados::AioCompletion *rc = impl->c;
  bool finish = false;

  impl->lock.lock();

  int ret = rc->get_return_value();

  // done with the rados completion
  rc->release();

  assert(impl->type == ZLOG_AIO_APPEND);

  if (ret == Backend::CLS_ZLOG_OK) {
    /*
     * Append was successful. We're done.
     */
    if (impl->pposition) {
      *impl->pposition = impl->position;
    }
    ret = 0;
    finish = true;
  } else if (ret == Backend::CLS_ZLOG_STALE_EPOCH) {
    /*
     * We'll need to try again with a new epoch.
     */
    ret = impl->log->RefreshProjection();
    if (ret)
      finish = true;
  } else if (ret == -EFBIG) {
    assert(impl->log->backend_ver == 2);
    impl->log->CreateNewStripe(impl->epoch);
    ret = impl->log->RefreshProjection();
    if (ret)
      finish = true;
  } else if (ret < 0) {
    /*
     * Encountered a RADOS error.
     */
    finish = true;
  } else {
    assert(ret == Backend::CLS_ZLOG_READ_ONLY);
  }

  /*
   * Try append again with a new position. This can happen if above there is a
   * stale epoch that we refresh, or if the position was marked read-only.
   */
  if (!finish) {
    // if we are appending, get a new position
    uint64_t position;
    ret = impl->log->CheckTail(&position, true);
    if (ret)
      finish = true;
    else
      impl->position = position;

    // we are still good. build a new aio
    if (!finish) {
      uint64_t epoch;
      std::string oid;
      impl->log->mapper_.FindObject(impl->position, &oid, &epoch);

      // refresh
      impl->epoch = epoch;

      impl->c = librados::Rados::aio_create_completion(impl, NULL, aio_safe_cb_append);
      assert(impl->c);
      // don't need impl->get(): reuse reference

      // build and submit new op
      librados::ObjectWriteOperation op;
      impl->log->backend->write(op, epoch, impl->position, impl->bl);
      ret = impl->ioctx->aio_operate(oid, impl->c, &op);
      if (ret)
        finish = true;
    }
  }

  // complete aio if append success, or any error
  if (finish) {
    impl->retval = ret;
    impl->complete = true;
    impl->lock.unlock();
    if (impl->has_callback)
      impl->callback();
    impl->cond.notify_all();
    impl->lock.lock();
    impl->put_unlock();
    return;
  }

  impl->lock.unlock();
}

AioCompletion::~AioCompletion() {}

/*
 * This is a wrapper around AioCompletion that lets users of the public API
 * delete its AioCompletion without deleting the underlying AioCompletionImpl
 * which is referece counted.
 *
 * This could also be done by exposing a shared_ptr. Are there other ways?
 */
class AioCompletionImplWrapper : public zlog::AioCompletion {
 public:
  explicit AioCompletionImplWrapper(AioCompletionImpl *impl) :
    impl_(impl)
  {}

  ~AioCompletionImplWrapper() {
    impl_->Release();
  }

  void SetCallback(std::function<void()> callback) {
    impl_->SetCallback(callback);
  }

  void WaitForComplete() {
    impl_->WaitForComplete();
  }

  int ReturnValue() {
    return impl_->ReturnValue();
  }

  AioCompletionImpl *impl_;
};

zlog::AioCompletion *Log::aio_create_completion(
    std::function<void()> callback)
{
  AioCompletionImpl *impl = new AioCompletionImpl;
  impl->has_callback = true;
  impl->callback = callback;
  return new AioCompletionImplWrapper(impl);
}

zlog::AioCompletion *Log::aio_create_completion()
{
  AioCompletionImpl *impl = new AioCompletionImpl;
  impl->has_callback = false;
  return new AioCompletionImplWrapper(impl);
}

/*
 * The retry for AioAppend is coordinated through the aio_safe_cb callback
 * which will dispatch a new rados operation.
 */
int LogImpl::AioAppend(AioCompletion *c, ceph::bufferlist& data,
    uint64_t *pposition)
{
  // initial position guess
  uint64_t position;
  int ret = CheckTail(&position, true);
  if (ret)
    return ret;

  AioCompletionImplWrapper *wrapper =
    reinterpret_cast<AioCompletionImplWrapper*>(c);
  AioCompletionImpl *impl = wrapper->impl_;

  impl->log = this;
  impl->bl = data;
  impl->position = position;
  impl->pposition = pposition;
  impl->ioctx = ioctx_;
  impl->type = ZLOG_AIO_APPEND;

  uint64_t epoch;
  std::string oid;
  mapper_.FindObject(position, &oid, &epoch);

  // used to identify if state changes have occurred since dispatching the
  // request in order to avoid reconfiguration later (important when lots of
  // threads or contexts try to do the same thing).
  impl->epoch = epoch;

  impl->get(); // rados aio now has a reference
  impl->c = librados::Rados::aio_create_completion(impl, NULL,
      AioCompletionImpl::aio_safe_cb_append);
  assert(impl->c);

  librados::ObjectWriteOperation op;
  backend->write(op, epoch, position, data);

  ret = ioctx_->aio_operate(oid, impl->c, &op);
  /*
   * Currently aio_operate never fails. If in the future that changes then we
   * need to make sure that references to impl and the rados completion are
   * cleaned up correctly.
   */
  assert(ret == 0);

  return ret;
}

int LogImpl::AioRead(uint64_t position, AioCompletion *c,
    ceph::bufferlist *pbl)
{
  AioCompletionImplWrapper *wrapper =
    reinterpret_cast<AioCompletionImplWrapper*>(c);
  AioCompletionImpl *impl = wrapper->impl_;

  impl->log = this;
  impl->pbl = pbl;
  impl->position = position;
  impl->ioctx = ioctx_;
  impl->type = ZLOG_AIO_READ;

  impl->get(); // rados aio now has a reference
  impl->c = librados::Rados::aio_create_completion(impl, NULL,
      AioCompletionImpl::aio_safe_cb_read);
  assert(impl->c);

  uint64_t epoch;
  std::string oid;
  mapper_.FindObject(position, &oid, &epoch);

  librados::ObjectReadOperation op;
  backend->read(op, epoch, position);

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
