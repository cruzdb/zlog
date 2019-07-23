#include "view_manager.h"
#include "log_impl.h"
#include <iterator>
#include <numeric>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include "libzlog/zlog_generated.h"
#include "log_backend.h"

// TODO
//  - add primitive for getting latest view

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

  // startup viewreader
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
  // read: the current view
  auto curr_view = view();

  // TODO: what is the initial state of the view/object_map for brand new logs?
  // there is a view created in stable storage for new logs, but it doesn't
  // appear the actualy log instance has it loaded initially. are we just
  // getting lucky that it's read up before hitting this?

  // modify: a new view that maps the position
  auto new_view = curr_view->expand_mapping(position, options_);
  if (!new_view) {
    return 0;
  }

  // TODO: it would be good track information that let us identify scenarios
  // when lots of threads or async ops are producing a thundering herd to
  // propose a new view. if this is occuring then we can optimize by
  // deduplicating the requests. this shouldn't be an issue when double
  // buffering view creation is working well.

  // write: the new view as the next epoch
  auto data = new_view->encode();
  const auto next_epoch = curr_view->epoch() + 1;
  int ret = backend_->ProposeView(next_epoch, data);
  if (!ret || ret == -ESPIPE) {
    update_current_view(curr_view->epoch(), true);
    if (!ret) {
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
    }
    return 0;
  }

  // ret == -ENOENT: this would imply that the hoid doesn't exist or isn't
  // initialized, which should have occurred when the log was created. this is
  // an error that should not be caught or handled.

  return ret;
}

int ViewManager::seal_stripe(const Stripe& stripe, uint64_t epoch,
    uint64_t *pposition, bool *pempty) const
{
  auto& oids = stripe.oids();
  assert(!oids.empty());

  for (auto& oid : oids) {
    int ret = backend_->Seal(oid, epoch);
    if (ret < 0) {
      return ret;
    }
  }

  bool stripe_empty = true;
  // max pos only defined for non-empty stripe
  uint64_t stripe_max_pos = 0;

  for (auto& oid : oids) {
    bool empty;
    uint64_t max_pos;
    int ret = backend_->MaxPos(oid, epoch, &max_pos, &empty);
    if (ret < 0) {
      return ret;
    }

    if (empty) {
      continue;
    }

    stripe_empty = false;
    stripe_max_pos = std::max(stripe_max_pos, max_pos);
  }

  if (pempty) {
    *pempty = stripe_empty;
  }

  if (pposition) {
    if (!stripe_empty) {
      *pposition = stripe_max_pos;
    }
  }

  return 0;
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

int ViewManager::propose_sequencer()
{
  // read: the current view
  auto curr_view = view();
  const auto next_epoch = curr_view->epoch() + 1;

  bool empty = true;
  // max pos only defined for non-empty log
  uint64_t max_pos;

  // find the maximum position written. the maximum position written is
  // contained in the first non-empty stripe scanning in reverse, beginning with
  // the stripe that maps the maximum possible position for the current view.

  std::vector<uint64_t> stripe_ids(curr_view->object_map().num_stripes());
  std::iota(std::begin(stripe_ids), std::end(stripe_ids), 0);

  auto it = stripe_ids.crbegin();
  for (; it != stripe_ids.crend(); it++) {
    const auto stripe = curr_view->object_map().stripe_by_id(*it);
    int ret = seal_stripe(stripe, next_epoch, &max_pos, &empty);
    if (ret < 0) {
      if (ret == -ESPIPE) {
        update_current_view(curr_view->epoch(), true);
        return 0;
      }
      return ret;
    }

    if (empty) {
      continue;
    }

    it++;
    break;
  }

  assert(!empty || it == stripe_ids.crend());

  // seal all other stripes. this is not to guarantee that the max is valid, but
  // rather to signal to clients connected / using other sequencers that they
  // should grab a new view to see the new sequencer.
  for (; it != stripe_ids.crend(); it++) {
    const auto stripe = curr_view->object_map().stripe_by_id(*it);
    int ret = seal_stripe(stripe, next_epoch, nullptr, nullptr);
    if (ret < 0) {
      if (ret == -ESPIPE) {
        update_current_view(curr_view->epoch(), true);
        return 0;
      }
      return ret;
    }
  }

  // new sequencer configuration.  the epoch used here is the epoch at which the
  // new seq takes affect. this controls the validitiy of seq_config.position
  // since the sequencer info is copied into new views. that is, a sequencer is
  // only initialized once when the initial epoch and view epoch are equal. XXX:
  // maybe we could solve this odd scenario by clearing the initial seq position
  // on copy, or breaking out into different data structures?
  SequencerConfig seq_config(
      next_epoch,
      backend_->token(),
      empty ? 0 : (max_pos + 1));

  // modify: the view by setting a new sequencer configuration
  auto new_view = curr_view->set_sequencer_config(seq_config);

  // write: the proposed new view
  auto data = new_view.encode();
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
