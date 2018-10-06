#include "log_impl.h"

#include <condition_variable>
#include <mutex>
#include "zlog/backend.h"

namespace zlog {

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
  std::function<void()> callback;
  uint64_t position;
  std::string data;

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
  std::string *datap;

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
    callback_complete = false;
    this->callback = callback;
  }

  static void aio_safe_cb_read(void *arg, int ret);
  static void aio_safe_cb_write(void *arg, int ret);
};

void AioCompletionImpl::aio_safe_cb_read(void *arg, int ret)
{
  AioCompletionImpl *impl = (AioCompletionImpl*)arg;
  bool finish;

  impl->lock.lock();

  if (ret == 0) {
    // success. return data to caller
    finish = true;
    if (impl->datap && !impl->data.empty()) {
      impl->datap->swap(impl->data);
    }
  } else if (ret == -ESPIPE) {
    // try again after refreshing view
    finish = false;
    impl->log->striper.refresh();
  } else if (ret < 0) {
    // return error to caller
    // -ENOENT  // not-written
    // -ENODATA // invalidated
    // other: rados error
    finish = true;
  } else if (ret == -ENOENT) {
    // well, fixing this crap AIO impl will need to happen soon. Here we'd
    // want to seal, but we aren't. It's not gonna fit in easily to this model
    // of aio handling.
    assert(0);
  } else {
    // unexpected return code
    assert(0);
    ret = -EIO;
    finish = true;
  }

  if (!finish) {
    while (true) {
      const auto view = impl->log->striper.view();
      const auto oid = view->object_map.map(impl->position);
      if (!oid) {
        ret = impl->log->striper.ensure_mapping(impl->position);
        if (ret < 0) {
          break;
        }
        continue;
      }

      // don't need impl->get(): reuse reference
      ret = impl->backend->AioRead(*oid, view->epoch(), impl->position, 0,
          &impl->data, impl, AioCompletionImpl::aio_safe_cb_read);
      break;
    }

    if (ret)
      finish = true;
  }

  if (finish) {
    impl->retval = ret;
    impl->complete = true;
    impl->lock.unlock();
    if (impl->callback)
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
  bool finish;

  impl->lock.lock();

  if (ret == 0) {
    // success. return position to caller.
    finish = true;
    if (impl->pposition) {
      *impl->pposition = impl->position;
    }
  } else if (ret == -ESPIPE) {
    // try again with a new log view
    finish = false;
    impl->log->striper.refresh();
  } else if (ret < 0 && ret != -EROFS) {
    // an error occured that should be returned to the user. for -EROFS the
    // append is retried at a new position.
    finish = true;
  } else if (ret == -ENOENT) {
    // well, fixing this crap AIO impl will need to happen soon. Here we'd
    // want to seal, but we aren't. It's not gonna fit in easily to this model
    // of aio handling.
    assert(0);
  } else {
    assert(0);
    ret = -EIO;
    finish = true;
  }

  if (!finish) {
    while (true) {
      const auto view = impl->log->striper.view();

      uint64_t position = 0;
      assert(0);
      // well, we need to fix the aio stuff...

      const auto oid = view->object_map.map(position);
      if (!oid) {
        ret = impl->log->striper.ensure_mapping(position);
        if (ret < 0) {
          break;
        }
        continue;
      }

      // don't need impl->get(): reuse reference
      impl->position = position;
      ret = impl->backend->AioWrite(*oid, view->epoch(), impl->position, 0,
          Slice(impl->data.data(), impl->data.size()), impl,
          AioCompletionImpl::aio_safe_cb_write);
    }

    if (ret)
      finish = true;
  }

  if (finish) {
    impl->retval = ret;
    impl->complete = true;
    impl->lock.unlock();
    if (impl->callback)
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
 * which is reference counted.
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
  impl->callback_complete = false;
  impl->callback = callback;
  return new AioCompletionImplWrapper(impl);
}

zlog::AioCompletion *Log::aio_create_completion()
{
  AioCompletionImpl *impl = new AioCompletionImpl;
  impl->callback_complete = true;
  return new AioCompletionImplWrapper(impl);
}

int LogImpl::AioAppend(AioCompletion *c, const Slice& data,
    uint64_t *pposition)
{
  while (true) {
    const auto view = striper.view();

    uint64_t position;
    if (view->seq) {
      position = view->seq->check_tail(true);
    } else {
      int ret = striper.propose_sequencer(view, options);
      if (ret && ret != -ESPIPE) {
        return ret;
      }
      striper.refresh(view->epoch());
      continue;
    }

    const auto oid = view->object_map.map(position);
    if (!oid) {
      int ret = striper.ensure_mapping(position);
      if (ret < 0) {
        return ret;
      }
      continue;
    }

    AioCompletionImplWrapper *wrapper =
      reinterpret_cast<AioCompletionImplWrapper*>(c);
    AioCompletionImpl *impl = wrapper->impl_;

    impl->log = this;
    impl->data.assign(data.data(), data.size());
    impl->position = position;
    impl->pposition = pposition;
    impl->backend = backend;
    impl->get(); // backend now has a reference

    int ret = backend->AioWrite(*oid, view->epoch(), position, 0, data,
        impl, AioCompletionImpl::aio_safe_cb_write);
    assert(ret == 0);

    return ret;
  }
}

int LogImpl::AioRead(uint64_t position, AioCompletion *c,
    std::string *datap)
{
  while (true) {
    const auto view = striper.view();
    const auto oid = view->object_map.map(position);
    if (!oid) {
      int ret = striper.ensure_mapping(position);
      if (ret < 0) {
        return ret;
      }
      continue;
    }

    AioCompletionImplWrapper *wrapper =
      reinterpret_cast<AioCompletionImplWrapper*>(c);
    AioCompletionImpl *impl = wrapper->impl_;
  
    impl->log = this;
    impl->datap = datap;
    impl->position = position;
    impl->backend = backend;
    impl->get(); // backend now has a reference
  
    int ret = backend->AioRead(*oid, view->epoch(), position, 0, &impl->data,
        impl, AioCompletionImpl::aio_safe_cb_read);
    assert(ret == 0);

    return ret;
  }
}

}
