#include "libzlog/view_reader.h"
#include "include/zlog/backend.h"
#include <iostream>

namespace zlog {

std::unique_ptr<ViewReader> ViewReader::open(
    const std::shared_ptr<Backend> backend,
    const std::string& hoid,
    const std::string& prefix,
    const std::string& secret,
    const Options& options)
{
  std::unique_ptr<VersionedView> latest_view;

  // TODO factor out and share with refresh thread
  // TODO backend wrapper for hoid, prefix, log name

  while (true) {
    const auto epoch = (latest_view ? latest_view->epoch() : 0) + 1;

    std::map<uint64_t, std::string> views;
    int ret = backend->ReadViews(hoid, epoch, 1, &views);
    if (ret) {
      return nullptr;
    }

    if (views.empty()) {
      break;
    }

    const auto it = views.crbegin();
    if (it == views.crend()) {
      return nullptr;
    }

    latest_view = std::unique_ptr<VersionedView>(
        new VersionedView(prefix, it->first, it->second));
  }

  if (!latest_view) {
    return nullptr;
  }

  return std::unique_ptr<ViewReader>(
      new ViewReader(backend, hoid, prefix, secret, options, std::move(latest_view)));
}

ViewReader::ViewReader(
    const std::shared_ptr<Backend> backend,
    const std::string& hoid,
    const std::string& prefix,
    const std::string& secret,
    const Options& options,
    std::unique_ptr<const VersionedView> view) :
  shutdown_(false),
  backend_(backend),
  hoid_(hoid),
  prefix_(prefix),
  secret_(secret),
  options_(options),
  view_(std::move(view)),
  refresh_thread_(std::thread(&ViewReader::refresh_entry_, this))
{
  assert(view_);
}

ViewReader::~ViewReader()
{
  {
    std::lock_guard<std::mutex> lk(lock_);
    assert(shutdown_);
    assert(refresh_waiters_.empty());
  }
  assert(!refresh_thread_.joinable());
}

void ViewReader::shutdown()
{
  {
    std::lock_guard<std::mutex> lk(lock_);
    shutdown_ = true;
  }
  refresh_cond_.notify_one();
  refresh_thread_.join();
}

void ViewReader::refresh_entry_()
{
  while (true) {
    uint64_t current_epoch;

    {
      std::unique_lock<std::mutex> lk(lock_);

      refresh_cond_.wait(lk, [&] {
        return !refresh_waiters_.empty() || shutdown_;
      });

      if (shutdown_) {
        for (auto waiter : refresh_waiters_) {
          waiter->done = true;
          waiter->cond.notify_one();
        }
        refresh_waiters_.clear();
        break;
      }

      assert(view_);
      current_epoch = view_->epoch();
    }

    // from which epoch should we start reading updates? note that in the
    // current version of zlog there are no incremental view updates, so it
    // would be sufficient to add an interface to retrieve the latest view.
    // however adding incremental updates is future work, so for now we just eat
    // the overhead of reading old views and tossing them away since that
    // machinary will eventually be needed.
    uint64_t epoch = current_epoch + 1;

    // read views at or after epoch
    std::map<uint64_t, std::string> views;
    int ret = backend_->ReadViews(hoid_, epoch,
        options_.max_refresh_views_read, &views);
    if (ret) {
      std::cerr << "read views error " << ret << std::endl;
      continue;
    }

    // no newer views were found. notify the waiters.
    if (views.empty()) {
      std::list<RefreshWaiter*> waiters;
      {
        std::lock_guard<std::mutex> lk(lock_);
        waiters.swap(refresh_waiters_);
      }
      for (auto it = waiters.begin(); it != waiters.end();) {
        const auto waiter = *it;
        // trying to make this locking fine grained to avoid blocking clients
        // is admirable, but really we probably just need a finger grained lock
        // to protect the waiters list rather than lock/unlock/lock/unlock/...
        std::lock_guard<std::mutex> lk(lock_);
        if (current_epoch > waiter->epoch) {
          waiter->done = true;
          waiter->cond.notify_one();
          it = waiters.erase(it);
        } else {
          it++;
        }
      }
      if (!waiters.empty()) {
        std::lock_guard<std::mutex> lk(lock_);
        refresh_waiters_.splice(refresh_waiters_.begin(), waiters);
      }
      // XXX: if a new waiter showed up while we were waking up waiters from the
      // copy made above, then when we continue we'll loop back around if there
      // are still waiters. however, when we move to a notify/watch method that
      // avoids spinning, be careful here to make sure that new waiters are
      // handled before blocking to wait on updates.
      continue;
    }

    // sanity check that there are no missing views
    for (const auto& view : views) {
      if (view.first != epoch) {
        assert(0);
        exit(0);
        return;
      }
      epoch++;
    }

    // grab the newest view in the batch
    const auto it = views.crbegin();
    assert(it != views.crend());

    auto new_view = std::make_shared<VersionedView>(prefix_, it->first, it->second);

    if (new_view->seq_config()) {
      if (new_view->seq_config()->secret() == secret_) { // we should be the active seq
        if (new_view->seq_config()->epoch() == it->first) {
          new_view->seq = std::make_shared<Sequencer>(it->first,
              new_view->seq_config()->position());
        } else {
          assert(new_view->seq_config()->epoch() < it->first);
          std::lock_guard<std::mutex> lk(lock_);
          assert(view_);
          assert(view_->seq);
          assert(view_->seq_config());
          assert(view_->seq_config()->epoch() == new_view->seq_config()->epoch());
          assert(view_->seq->epoch() == view_->seq_config()->epoch());
          // be careful that this isn't copying the state of the sequencer. when
          // this comment was written, this was copying a shared_ptr to the
          // state which is fine. the issue that other threads may be
          // simultaneously incrementing the sequencer and we don't want to miss
          // those increments when setting up the new view.
          new_view->seq = view_->seq;
        }
      } else {
        new_view->seq = nullptr;
      }
    } else {
      new_view->seq = nullptr;
    }

    std::lock_guard<std::mutex> lk(lock_);
    view_ = std::move(new_view);
  }
}

std::shared_ptr<const VersionedView> ViewReader::view() const
{
  std::lock_guard<std::mutex> lk(lock_);
  assert(view_);
  return view_;
}

void ViewReader::update_current_view(const uint64_t epoch)
{
  std::unique_lock<std::mutex> lk(lock_);
  if (shutdown_) {
    return;
  }
  RefreshWaiter waiter(epoch);
  // XXX: is it necessary to hold the lock here to ensure that the epoch set
  // above in waiter is always seen by by the refresh thread, even though the
  // refresh thread will always grab the lock too to discover the waiter?  need
  // to go do a quick refresher on the memory consistency semantics.
  refresh_waiters_.emplace_back(&waiter);
  refresh_cond_.notify_one();
  waiter.cond.wait(lk, [&waiter] { return waiter.done; });
}

}
