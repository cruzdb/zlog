#include "libzlog/view_reader.h"
#include "include/zlog/backend.h"
#include <iostream>

// TODO: client requests that see a nullptr sequencer shoudl block and wait for
// updates
// TODO: use a smarter index for epoch waiters
// TODO backend wrapper for hoid, prefix, log name
// TODO build a log's initial view for exclusive sequencers

namespace zlog {

ViewReader::ViewReader(
    const std::shared_ptr<Backend> backend,
    const std::string& hoid,
    const std::string& prefix,
    const std::string& secret,
    const Options& options) :
  shutdown_(false),
  backend_(backend),
  hoid_(hoid),
  prefix_(prefix),
  secret_(secret),
  options_(options),
  view_(nullptr),
  refresh_thread_(std::thread(&ViewReader::refresh_entry_, this))
{
}

ViewReader::~ViewReader()
{
  {
    std::lock_guard<std::mutex> lk(lock_);
    if (shutdown_) {
      assert(refresh_waiters_.empty());
      assert(!refresh_thread_.joinable());
      return;
    }
  }

  shutdown();

  std::lock_guard<std::mutex> lk(lock_);
  assert(shutdown_);
  assert(refresh_waiters_.empty());
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
    }

    refresh_view();

    const auto current_view = view();
    if (!current_view) {
      continue;
    }

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
      if (current_view->epoch() > waiter->epoch) {
        waiter->done = true;
        waiter->cond.notify_one();
        it = waiters.erase(it);
      } else {
        it++;
      }
    }

    // add any waiters that weren't notified back into the master list. don't
    // naively replace the list as other waiters may have shown up recently.
    if (!waiters.empty()) {
      std::lock_guard<std::mutex> lk(lock_);
      refresh_waiters_.splice(refresh_waiters_.begin(), waiters);
    }
  }
}

std::shared_ptr<const VersionedView> ViewReader::view() const
{
  std::lock_guard<std::mutex> lk(lock_);
  return view_;
}

void ViewReader::wait_for_newer_view(const uint64_t epoch)
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

std::unique_ptr<VersionedView> ViewReader::get_latest_view() const
{
  std::map<uint64_t, std::string> views;
  int ret = backend_->ReadViews(hoid_, 0, 1, &views);
  if (ret) {
    return nullptr;
  }

  const auto it = views.crbegin();
  if (it == views.crend()) {
    // this would happen if there are no views
    return nullptr;
  }

  return std::unique_ptr<VersionedView>(
      new VersionedView(prefix_, it->first, it->second));
}

void ViewReader::refresh_view()
{
  auto latest_view = get_latest_view();
  if (!latest_view) {
    return;
  }
  assert(!latest_view->seq);

  std::lock_guard<std::mutex> lk(lock_);

  if (view_) {
    assert(latest_view->epoch() >= view_->epoch());
    if (latest_view->epoch() == view_->epoch()) {
      return;
    }
  }

  // if the latest view has a sequencer config and secret that matches this log
  // client instance, then we will become a sequencer / exclusive writer.
  if (latest_view->seq_config() &&
      latest_view->seq_config()->secret() == secret_) {

    // there are two cases for initializing the new view's sequencer:
    //
    //   1) reuse sequencer from previous view
    //   2) create a new sequencer instance
    //
    // if a previous view has a sequencer with the same secret, then we might be
    // able to reuse it. however, if the previous view that we have and the
    // latest view are separated by views with _other_ sequencers in the log,
    // but which we haven't observed, then we need to take that into account.
    // in order to catch this scenario, we also check that the previous view has
    // an initialization epoch that matches the epoch in the latest view's
    // sequencer config.
    //
    // the sequencer config in a view either copied or a new sequencer config is
    // proposed. whenver a sequencer config is successfully proposed, it's
    // initialization epoch will be unique (even for different proposals from
    // the same log client). so, if the secret and the initialization epoch are
    // equal, then we can be assured that the sequencer hasn't changed and we
    // can reuse the state.
    //
    if (view_ &&
        view_->seq_config() &&
        view_->seq_config()->secret() == secret_ &&
        view_->seq_config()->epoch() == latest_view->seq_config()->epoch()) {
      //
      // note about thread safety. here we copy the pointer to the existing
      // sequencer which may be in-use concurrently. it wouldn't be sufficient
      // to create a new sequencer object initialized with the existing state
      // (we could miss updates to the seq state until all new threads saw the
      // new view) unless concurrent updates were blocked by a lock, but that
      // would introduce a lock on the i/o path.
      //
      assert(view_->seq);
      latest_view->seq = view_->seq;
    } else {
      // create a new instance for this sequencer
      latest_view->seq = std::make_shared<Sequencer>(latest_view->epoch(),
          latest_view->seq_config()->position());
    }
  }

  view_ = std::move(latest_view);
}

}
