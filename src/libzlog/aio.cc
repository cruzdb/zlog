#include "log_impl.h"

#include <condition_variable>
#include <mutex>
#include "zlog/backend.h"

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
  bool callback_complete;
  bool released;

  /*
   * base log and rados completion
   */
  LogImpl *log;
  std::shared_ptr<Backend> backend;

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
  std::string data;
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
  std::string *datap;
  Cache* cache;

  AioCompletionImpl() :
    ref(1), complete(false), callback_complete(false), released(false), retval(0)
  {}

  void WaitForComplete() {
    std::unique_lock<std::mutex> l(lock);
    cond.wait(l, [&]{ return complete && callback_complete; });
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
    callback_complete = false;
    this->callback = callback;
  }

  static void aio_safe_cb_read(void *arg, int ret);
  static void aio_safe_cb_write(void *arg, int ret);
};

void AioCompletionImpl::aio_safe_cb_read(void *arg, int ret)
{
  AioCompletionImpl *impl = (AioCompletionImpl*)arg;
  bool finish = false;

  impl->lock.lock();

  assert(impl->type == ZLOG_AIO_READ);

  if (ret == 0) {
    /*
     * Read was successful. We're done.
     */
    if (impl->datap && !impl->data.empty()) {
      impl->datap->swap(impl->data);
    }
    
    impl->cache->put(impl->position, Slice(*(impl->datap)));

    ret = 0;
    finish = true;
  } else if (ret == -ESPIPE) {
    /*
     * We'll need to try again with a new epoch.
     */
    ret = impl->log->UpdateView();
    if (ret)
      finish = true;
  } else if (ret < 0) {
    // -ENOENT  // not-written
    // -ENODATA // invalidated
    // other: rados error
    finish = true;
  } else {
    assert(0);
    ret = -EIO;
    finish = true;
  }

  /*
   * Try append again with a new position. This can happen if above there is a
   * stale epoch that we refresh, or if the position was marked read-only.
   */
  if (!finish) {
    auto mapping = impl->log->striper.MapPosition(impl->position);
    while (!mapping) {
      ret = impl->log->ExtendMap();
      if (ret)
        break;
      mapping = impl->log->striper.MapPosition(impl->position);
    }

    // don't need impl->get(): reuse reference

    if (mapping) {
      // submit new aio op
      ret = impl->backend->AioRead(mapping->oid, mapping->epoch, impl->position,
          mapping->width, mapping->max_size, &impl->data,
          impl, AioCompletionImpl::aio_safe_cb_read);
    }

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
    impl->callback_complete = true;
    impl->cond.notify_all();
    impl->lock.lock();
    impl->put_unlock();
    return;
  }

  impl->lock.unlock();
}

void AioCompletionImpl::aio_safe_cb_write(void *arg, int ret)
{
  AioCompletionImpl *impl = (AioCompletionImpl*)arg;
  bool finish = false;

  impl->lock.lock();

  assert(impl->type == ZLOG_AIO_APPEND);

  if (ret == 0) {
    /*
     * Append was successful. We're done.
     */
    if (impl->pposition) {
      *impl->pposition = impl->position;
    }
    impl->cache->put(*(impl->pposition), impl->data);

    ret = 0;
    finish = true;
  } else if (ret == -ESPIPE) {
    /*
     * We'll need to try again with a new epoch.
     */
    ret = impl->log->UpdateView();
    if (ret)
      finish = true;
  } else if (ret < 0 && ret != -EROFS) {
    /*
     * Encountered a RADOS error.
     */
    finish = true;
  } else {
    assert(0);
    ret = -EIO;
    finish = true;
  }

  /*
   * Try append again with a new position. This can happen if above there is a
   * stale epoch that we refresh, or if the position was marked read-only.
   */
  if (!finish) {
    // if we are appending, get a new position
    uint64_t position;
    uint64_t seq_epoch;
    boost::optional<Striper::Mapping> mapping;
    while (true) {
      ret = impl->log->CheckTail(&position, &seq_epoch, true);
      if (ret) {
        finish = true;
        break;
      }
      mapping = impl->log->striper.MapPosition(position);
      while (!mapping) {
        ret = impl->log->ExtendMap();
        if (ret)
          break;
        mapping = impl->log->striper.MapPosition(position);
      }
      if (ret) {
        finish = true;
        break;
      }
      if (seq_epoch != mapping->epoch) {
        std::cerr << "trying new seq" << std::endl;
        continue;
      }

      break;
    }

    // we are still good. build a new aio
    if (!finish) {
      impl->position = position;

      // refresh
      impl->epoch = mapping->epoch;

      // don't need impl->get(): reuse reference

      // submit new aio op
      ret = impl->backend->AioWrite(mapping->oid, mapping->epoch, impl->position,
          mapping->width, mapping->max_size,
          Slice(impl->data.data(), impl->data.size()),
          impl, AioCompletionImpl::aio_safe_cb_write);
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
    impl->callback_complete = true;
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
  impl->callback_complete = false;
  impl->callback = callback;
  return new AioCompletionImplWrapper(impl);
}

zlog::AioCompletion *Log::aio_create_completion()
{
  AioCompletionImpl *impl = new AioCompletionImpl;
  impl->has_callback = false;
  impl->callback_complete = true;
  return new AioCompletionImplWrapper(impl);
}

/*
 * The retry for AioAppend is coordinated through the aio_safe_cb callback
 * which will dispatch a new rados operation.
 */
int LogImpl::AioAppend(AioCompletion *c, const Slice& data,
    uint64_t *pposition)
{
  // initial guess. see #194 about moving sequencer call into the callback for
  // full async behavior.
  uint64_t position;
  uint64_t seq_epoch;
  boost::optional<Striper::Mapping> mapping;
  while (true) {
    int ret = CheckTail(&position, &seq_epoch, true);
    if (ret)
      return ret;

    mapping = striper.MapPosition(position);
    while (!mapping) {
      ret = ExtendMap();
      if (ret)
        return ret;
      mapping = striper.MapPosition(position);
    }

    if (seq_epoch != mapping->epoch) {
      std::cerr << "retry with new seq" << std::endl;
      continue;
    }

    break;
  }

  AioCompletionImplWrapper *wrapper =
    reinterpret_cast<AioCompletionImplWrapper*>(c);
  AioCompletionImpl *impl = wrapper->impl_;

  impl->log = this;
  impl->data.assign(data.data(), data.size());
  impl->position = position;
  impl->pposition = pposition;
  impl->backend = backend;
  impl->type = ZLOG_AIO_APPEND;
  impl->cache = cache;

  // used to identify if state changes have occurred since dispatching the
  // request in order to avoid reconfiguration later (important when lots of
  // threads or contexts try to do the same thing).
  impl->epoch = mapping->epoch;

  impl->get(); // backend now has a reference

  int ret = backend->AioWrite(mapping->oid, mapping->epoch, position,
      mapping->width, mapping->max_size, data,
      impl, AioCompletionImpl::aio_safe_cb_write);
  /*
   * Currently aio_operate never fails. If in the future that changes then we
   * need to make sure that references to impl and the rados completion are
   * cleaned up correctly.
   */
  assert(ret == 0);

  return ret;
}

int LogImpl::AioRead(uint64_t position, AioCompletion *c,
    std::string *datap)
{


  AioCompletionImplWrapper *wrapper =
    reinterpret_cast<AioCompletionImplWrapper*>(c);
  AioCompletionImpl *impl = wrapper->impl_;

  
  impl->log = this;
  impl->datap = datap;
  impl->position = position;
  impl->backend = backend;
  impl->type = ZLOG_AIO_READ;
  impl->cache = cache;

  impl->get(); // backend now has a reference

  int cache_miss = cache->get(&position, datap);
  if(!cache_miss){

    int ret = 0;  
    impl->lock.lock();
    impl->retval = ret;
    impl->complete = true;
    impl->lock.unlock();
    if (impl->has_callback)
      impl->callback();
    impl->callback_complete = true;
    impl->cond.notify_all();
    impl->lock.lock();
    impl->put_unlock();

    return ret;
  }

  
  auto mapping = striper.MapPosition(position);
  while (!mapping) {
    int ret = ExtendMap();
    if (ret)
      return ret;
    mapping = striper.MapPosition(position);
  }

  int ret = backend->AioRead(mapping->oid, mapping->epoch, position,
      mapping->width, mapping->max_size, &impl->data,
      impl, AioCompletionImpl::aio_safe_cb_read);
  /*
   * Currently aio_operate never fails. If in the future that changes then we
   * need to make sure that references to impl and the rados completion are
   * cleaned up correctly.
   */
  assert(ret == 0);


  return ret;
}


}
