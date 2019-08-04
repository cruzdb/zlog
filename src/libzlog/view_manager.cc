#include "view_manager.h"
#include "log_impl.h"
#include <iterator>
#include <numeric>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include "libzlog/zlog_generated.h"
#include "log_backend.h"

namespace zlog {

ViewManager::ViewManager(const Options& options,
    std::shared_ptr<LogBackend> backend,
    std::unique_ptr<ViewReader> view_reader) :
  shutdown_(false),
  backend_(backend),
  options_(options),
  view_reader_(std::move(view_reader)),
  expand_pos_(boost::none)
{
  assert(backend_);
  assert(view_reader_);
  assert(view_reader_->view());

  expander_thread_ = std::thread(&ViewManager::expander_entry_, this);
  stripe_init_thread_ = std::thread(&ViewManager::stripe_init_entry_, this);
}

ViewManager::~ViewManager()
{
  {
    std::lock_guard<std::mutex> lk(lock_);
    assert(shutdown_);
  }
  assert(!expander_thread_.joinable());
  assert(!stripe_init_thread_.joinable());
}

void ViewManager::shutdown()
{
  {
    std::lock_guard<std::mutex> lk(lock_);
    shutdown_ = true;
  }

  // shutdown the view reader first to make sure that other helper threads
  // aren't blocked waiting on a new view when they are shutdown and joined.
  view_reader_->shutdown();

  expander_cond_.notify_one();
  stripe_init_cond_.notify_one();

  expander_thread_.join();
  stripe_init_thread_.join();
}

boost::optional<std::vector<std::pair<std::string, bool>>>
ViewManager::map_to(const std::shared_ptr<const View>& view, const uint64_t position,
    uint64_t& stripe_id, bool& done) const
{
  return view->object_map().map_to(position, stripe_id, done);
}

boost::optional<std::string> ViewManager::map(
    const std::shared_ptr<const View>& view,
    const uint64_t position)
{
  const auto mapping = view->object_map().map(position);
  const auto oid = mapping.first;
  const auto last_stripe = mapping.second;

  // oid, false -> return oid (fast return case)
  if (oid && !last_stripe) {
    return oid;
  }

  // oid, true -> expand(max view pos + 1)
  if (oid && last_stripe) {
    // asynchronsouly expand the view to map the next stripe. note that the
    // existence of a mapping for the position implies the objectmap is not
    // empty. calling max_position on a empty object map is undefined behavior.
    async_expand_view(view->object_map().max_position() + 1);
    return oid;
  }

  // none, true   -> not a valid combination
  // none, false  -> need to expand the mapping
  assert(!oid);
  assert(!last_stripe);

  // the position mapped past the view's maximum position, so the caller likely
  // can't make progress (e.g. if it is trying to append). at this point the
  // caller should attempt to expand the view / mapping.
  return boost::none;

  // TODO: since by definition the next stripe will be the last stripe in the
  // view, and because the striper attempts to "double buffer" stripe creation
  // to avoid faulting on a mapping in the hot path, it would make sense here as
  // a minor optimization for the caller to add two stripe: the target for this
  // mapping and the following. this is a minor optimization beacuse once the
  // view is extended the normal asynchronous double buffering will kick in
  // during the next I/O operation. this can be a flag on try_expand_view that's
  // true (2x expand) when faulting or false (1x expand) when its normal async
  // expanding.
}

int ViewManager::try_expand_view(const uint64_t position)
{
  int retries = 7;
  std::chrono::milliseconds delay(125);

  while (true) {
    // read the current view
    const auto curr_view = view();
    const auto next_epoch = curr_view->epoch() + 1;

    // build a new view that maps the target position
    const auto new_view = curr_view->expand_mapping(position, options_);
    if (!new_view) {
      return 0;
    }

    // write the new view as the next epoch
    const auto data = new_view->encode();
    int ret = backend_->ProposeView(next_epoch, data);

    if (!ret) {
      update_current_view(curr_view->epoch(), true);
      // we successfully proposed the new stripe, so schedule an initialization
      // job for the objects in the new stripe. it's possible that in the case
      // of ESPIPE (out-of-date epoch) that another proposer process (or the
      // auto view expander thread) created the target stripe but crashed (or in
      // the case of the auto view expander thread, it would be racing) before
      // initializing the stripe. ideally we could detect this (possibly with a
      // heuristic or flag in views) and schedule initialization. this is not
      // for correctness: client I/O path will do its own synchronous
      // initialization to make progress. the optimization is future work if
      // necessary: keeping stats on these scenarios would be useful.
      if (options_.init_stripe_on_create) {
        async_init_stripe(position);
      }
      return 0;
    }

    // we could have lost the proposal to a sequencer proposal or some other
    // view proposal. keep trying, but backoff first.
    if (ret == -ESPIPE) {
      update_current_view(curr_view->epoch(), true);
      if (--retries == 0) {
        // caller will look at the view again
        return 0;
      }
      {
        std::lock_guard<std::mutex> lk(lock_);
        if (shutdown_) {
          return -ESHUTDOWN;
        }
      }
      std::this_thread::sleep_for(delay);
      delay *= 2;
      continue;
    }

    return ret;
  }
}

int ViewManager::advance_min_valid_position(const uint64_t position)
{
  // read: the current view
  auto curr_view = view();

  // update: is the invalid range expanding?
  auto new_view = curr_view->advance_min_valid_position(position);
  if (!new_view) {
    return 0;
  }

  // write: the proposed new view
  auto data = new_view->encode();
  const auto next_epoch = curr_view->epoch() + 1;
  int ret = backend_->ProposeView(next_epoch, data);
  if (!ret || ret == -ESPIPE) {
    update_current_view(curr_view->epoch(), true);
    return 0;
  }

  return ret;
}

// no deduplication is performed here, but this is only triggered by the thread
// that successfully creates a new stripe, of which there should just be one per
// stripe. later if/when we try to optimize for the rare case of the stripe
// creator crashing before finishing initialization, we _might_ run into a case
// where we want to deduplicate the stripe init jobs.
void ViewManager::async_init_stripe(uint64_t position)
{
  std::lock_guard<std::mutex> lk(lock_);
  stripe_init_pos_.push_back(position);
  stripe_init_cond_.notify_one();
}

void ViewManager::stripe_init_entry_()
{
  while (true) {
    uint64_t position;
    {
      std::unique_lock<std::mutex> lk(lock_);

      stripe_init_cond_.wait(lk, [&] {
        return !stripe_init_pos_.empty() || shutdown_;
      });

      if (shutdown_) {
        break;
      }

      assert(!stripe_init_pos_.empty());
      position = stripe_init_pos_.front();
      stripe_init_pos_.pop_front();
    }

    auto v = view();
    auto stripe = v->object_map().map_stripe(position);
    if (!stripe) {
      continue;
    }

    auto& oids = stripe->oids();
    assert(!oids.empty());

    // TODO: this is a case for not using Seal to initialize objects. if the
    // objects in the stripe are already initialized, then it is common for this
    // initialization job to be using a newer epoch/view, which means that the
    // epoch will be bumped on the objects (for no good reason) in the stripe
    // even though all we really wanted to do is initialize if not already
    // initialized.
    for (auto& oid : oids) {
      backend_->Seal(oid, v->epoch());
    }
  }
}

void ViewManager::expander_entry_()
{
  while (true) {
    std::unique_lock<std::mutex> lk(lock_);

    expander_cond_.wait(lk, [&] {
      return expand_pos_ || shutdown_;
    });

    if (shutdown_) {
      break;
    }

    assert(expand_pos_);
    const auto position = *expand_pos_;
    lk.unlock();

    const auto v = view();
    const auto mapping = v->object_map().map(position);
    if (!mapping.first) {
      // TODO: in the revampped version of the io path, we want to avoid
      // spinning. try expand view uses a retry with backoff, but uncaught
      // errors like other io errors or something would cause this thread to
      // spin.
      try_expand_view(position);
      continue;
    }

    lk.lock();
    assert(expand_pos_);
    if (*expand_pos_ > position) {
      continue;
    }
    expand_pos_ = boost::none;
  }
}

void ViewManager::async_expand_view(uint64_t position)
{
  std::unique_lock<std::mutex> lk(lock_);
  if (!expand_pos_ || position > *expand_pos_) {
    expand_pos_ = position;
    expander_cond_.notify_one();
  }
}

}
