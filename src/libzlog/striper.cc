#include "striper.h"
#include "log_impl.h"
#include <iterator>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>

#include "spdlog/spdlog.h"
#include "spdlog/sinks/stdout_color_sinks.h"

static auto console = spdlog::stdout_color_mt("console");

// How does a client learn about available sequencers?
//
//   - a dns entry with multiple records
//   - environment variables
//   - command line arguments
//   - configuration file
//   - etc...
//
// Once a sequencer is chosen, it should be added to the latest view. This is
// because when a new client is created it should be able to play nicely by
// using whatever was already configured.
//
// After a sequencer is chosen by a client (either from the log, or from some
// other source) it will send a message to this sequencer requesting service for
// the log being opened.
//
//   A sequencer will always try to become the active sequencer when asked. This
//   is a simple policy of last attempt wins. And this is ok in most cases since
//   new clients will attempt to contact the already configured sequencer.
//
// A sequencer becomes active for a log by adding itself to the new, latest
// view and then becoming active. It will seal the log during this process to
// box out other sequencers, and to find the maximum log position.
//
//   NOTE: we can seal all stripes, or optimize by tracking the maximum position
//   and then only sealing those which could be affected. This is an
//   optimization step we can add a GH issue for.
//
// A sequencer will add a unique value to the view so that clients can detect
// frauds.

// dns can point to a set of sequencer servers
// these sequencer servers _could_ organize to balance load
// when a sequencer server starts serving a log it adds its id to the view
// or the set of sequencer could be provided on a comamnd line or in a config
// file or added to a special log. initially, just have an environmetn variable
// with a single entry.
//
// pick a seqencer and request it for the log
// then after that its registered in the log for other clents to find
// or can be automatically moved between seqnecers for balancing, and the choice
// communicated throught he log
//
// seqeuncer should use hoid instead of log name
//
// a new log is created w/o a sequencer server specified
// created with a server
// opened
// reconfigured sequencer
// dns
// env vars
// created or changed into exclusive mode
//
// cli command creates a new log

// Log open in seq should use hoid


////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

namespace zlog {

std::vector<std::string> Stripe::make_oids(
    const std::string& prefix, uint64_t id, uint32_t width)
{
  std::vector<std::string> oids;
  oids.reserve(width);

  for (uint32_t i = 0; i < width; i++) {
    std::stringstream oid;
    oid << prefix << "." << id << "." << i;
    oids.emplace_back(oid.str());
  }

  return oids;
}

// TODO: refactor this with ObjectMap::map
boost::optional<Stripe> ObjectMap::map_stripe(uint64_t position) const
{
  if (!stripes_.empty()) {
    auto it = stripes_.upper_bound(position);
    it = std::prev(it);
    assert(it->first <= position);
    if (position <= it->second.max_position()) {
      return it->second;
    }
  }
  return boost::none;
}

// trim a single position vs trim from 0..N. do we fault in those objects? i
// think that we can just trim what we find, but if we trim way past the end we
// don't need to make new stripes? it would seem not to be necessary. but in
// that case, perhaps we should also just skip truncating and just delete the
// objects instead of special casing delete.

std::pair<boost::optional<std::string>, bool>
ObjectMap::map(const uint64_t position) const
{
  if (!stripes_.empty()) {
    auto it = stripes_.upper_bound(position);
    it = std::prev(it);
    assert(it->first <= position);
    if (position <= it->second.max_position()) {
      auto oid = it->second.map(position);
      auto last_stripe = std::next(it) == stripes_.end();
      return std::make_pair(oid, last_stripe);
    }
  }
  return std::make_pair(boost::none, false);
}

boost::optional<std::vector<std::pair<std::string, bool>>>
ObjectMap::map_to(const uint64_t position) const
{
  // the max position is not mapped
  if (!map(position).first) {
    return boost::none;
  }

  // first: object name
  // second: complete map?
  std::vector<std::pair<std::string, bool>> objects;

  for (auto it = stripes_.cbegin(); it != stripes_.cend(); it++) {
    const auto& stripe = it->second;
    const auto oids = stripe.oids();

    const auto min_pos_base = it->first;

    if (min_pos_base > position) {
      break;
    }

    const auto max_pos_base = stripe.max_position() - (stripe.width() - 1);

    for (uint32_t i = 0; i < stripe.width(); i++) {
      const auto max_pos = max_pos_base + i;
      if (max_pos <= position) {
        objects.push_back(std::make_pair(oids[i], true));
        continue;
      }

      const auto min_pos = min_pos_base + i;
      if (min_pos <= position) {
        objects.push_back(std::make_pair(oids[i], false));
        continue;
      }
    }
  }

  return objects;
}

bool ObjectMap::expand_mapping(const std::string& prefix,
    const uint64_t position, uint32_t stripe_width, uint32_t stripe_slots)
{
  if (map(position).first) {
    return false;
  }

  const uint64_t num_stripe_entries = (uint64_t)stripe_width * stripe_slots;
  assert(num_stripe_entries > 0);

  do {
    const auto it = stripes_.crbegin();
    const auto empty = it == stripes_.crend();
    const auto min_position = empty ? 0 : (it->second.max_position() + 1);
    const auto max_position = min_position + num_stripe_entries - 1;
    const auto stripe_id = next_stripe_id_++;
    stripes_.emplace(min_position,
        Stripe{prefix, stripe_id, stripe_width, max_position});
  } while (!map(position).first);

  return true;
}

uint64_t ObjectMap::max_position() const
{
  auto stripe = stripes_.crbegin();
  assert(stripe != stripes_.crend());
  return stripe->second.max_position();
}

Striper::Striper(LogImpl *log, const std::string& secret) :
  shutdown_(false),
  log_(log),
  secret_(secret),
  view_(std::make_shared<const View>()),
  expand_pos_(boost::none)
{
  refresh_thread_ = std::thread(&Striper::refresh_entry_, this);
  expander_thread_ = std::thread(&Striper::expander_entry_, this);
  stripe_init_thread_ = std::thread(&Striper::stripe_init_entry_, this);
}

Striper::~Striper()
{
  {
    std::lock_guard<std::mutex> lk(lock_);
    assert(shutdown_);
    assert(refresh_waiters_.empty());
  }
  assert(!refresh_thread_.joinable());
  assert(!expander_thread_.joinable());
  assert(!stripe_init_thread_.joinable());
}

std::shared_ptr<const View> Striper::view() const
{
  std::lock_guard<std::mutex> lk(lock_);
  assert(view_);
  return view_;
}

void Striper::shutdown()
{
  {
    std::lock_guard<std::mutex> lk(lock_);
    shutdown_ = true;
  }
  refresh_cond_.notify_one();
  expander_cond_.notify_one();
  stripe_init_cond_.notify_one();
  refresh_thread_.join();
  expander_thread_.join();
  stripe_init_thread_.join();
}

boost::optional<std::vector<std::pair<std::string, bool>>>
Striper::map_to(const std::shared_ptr<const View>& view,
    const uint64_t position)
{
  return view->object_map.map_to(position);
}

boost::optional<std::string> Striper::map(
    const std::shared_ptr<const View>& view,
    const uint64_t position)
{
  const auto mapping = view->object_map.map(position);
  const auto oid = mapping.first;
  const auto last_stripe = mapping.second;

  // oid, false -> return oid (fast return case)
  if (oid && !last_stripe) {
    return oid;
  }

  // oid, true -> expand(max view pos + 1)
  if (oid && last_stripe) {
    // asynchronsouly expand the view to map the next stripe
    async_expand_view(view->object_map.max_position() + 1);
    return oid;
  }

  // none, true   -> not a valid combination
  // none, false  -> expand(position)
  assert(!oid);
  assert(!last_stripe);

  // the position mapped past the view's maximum position. the caller can't make
  // progress, so we can immediately try to create a new view. since the
  // position will by definition map into a new stripe that is also the last
  // stripe in the new view, go ahead and create the target stripe and the
  // following stripe. XXX: this is a future enhancement. returning boost::none
  // here will cause the caller to expand the view to map the position, but
  // won't add an extra stripe until the next I/O occurs.
  return boost::none;
}

int Striper::try_expand_view(const uint64_t position)
{
  // read: the view into a mutable copy
  auto v = *view();
  const auto next_epoch = v.epoch() + 1;

  // modify: the object map to contain the position
  auto changed = v.object_map.expand_mapping(log_->prefix, position,
      log_->options.stripe_width, log_->options.stripe_slots);
  if (!changed) {
    return 0;
  }

  // TODO: it would be good track information that let us identify scenarios
  // when lots of threads or async ops are producing a thundering herd to
  // propose a new view. if this is occuring then we can optimize by
  // deduplicating the requests. this shouldn't be an issue when double
  // buffering view creation is working well.

  // write: the serialized view as a new epoch view
  auto data = v.serialize();
  int ret = log_->backend->ProposeView(log_->hoid, next_epoch, data);
  if (!ret || ret == -ESPIPE) {
    update_current_view(v.epoch());
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
      if (log_->options.init_stripe_on_create) {
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

int Striper::seal_stripe(const Stripe& stripe, uint64_t epoch,
    uint64_t *pposition, bool *pempty) const
{
  auto& oids = stripe.oids();
  assert(!oids.empty());

  for (auto& oid : oids) {
    int ret = log_->backend->Seal(oid, epoch);
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
    int ret = log_->backend->MaxPos(oid, epoch, &max_pos, &empty);
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

int Striper::advance_min_valid_position(const uint64_t position)
{
  // read: a mutable copy of the current view
  auto v = *view();
  const auto next_epoch = v.epoch() + 1;

  // is the invalid range expanding?
  if (position <= v.min_valid_position) {
    return 0;
  }

  // update the view
  v.min_valid_position = position;

  // write: the proposed new view
  auto data = v.serialize();
  int ret = log_->backend->ProposeView(log_->hoid, next_epoch, data);
  if (!ret || ret == -ESPIPE) {
    update_current_view(v.epoch());
    return 0;
  }

  return ret;
}

int Striper::propose_sequencer()
{
  // read: a mutable copy of the current view
  auto v = *view();
  const auto next_epoch = v.epoch() + 1;

  bool empty = true;
  // max pos only defined for non-empty log
  uint64_t max_pos;

  // find the maximum position written. the maximum position written is
  // contained in the first non-empty stripe scanning in reverse, beginning with
  // the stripe that maps the maximum possible position for the current view.
  const auto stripes = v.object_map.stripes();
  auto it = stripes.crbegin();
  for (; it != stripes.crend(); it++) {
    auto& stripe = it->second;
    int ret = seal_stripe(stripe, next_epoch, &max_pos, &empty);
    if (ret < 0) {
      if (ret == -ESPIPE) {
        update_current_view(v.epoch());
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

  assert(!empty || it == stripes.crend());

  // seal all other stripes. this is not to guarantee that the max is valid, but
  // rather to signal to clients connected / using other sequencers that they
  // should grab a new view to see the new sequencer.
  for (; it != stripes.crend(); it++) {
    auto& stripe = it->second;
    int ret = seal_stripe(stripe, next_epoch, nullptr, nullptr);
    if (ret < 0) {
      if (ret == -ESPIPE) {
        update_current_view(v.epoch());
        return 0;
      }
      return ret;
    }
  }

  // new sequencer configuration
  SequencerConfig seq_config;
  seq_config.secret = secret_;
  seq_config.position = empty ? 0 : (max_pos + 1);

  // this is the epoch at which the new seq takes affect. this controls the
  // validitiy of seq_config.position since the sequencer info is copied into
  // new views. that is, a sequencer is only initialized once when the initial
  // epoch and view epoch are equal. XXX: maybe we could solve this odd scenario
  // by clearing the initial seq position on copy, or breaking out into
  // different data structures?
  seq_config.epoch = next_epoch;

  // modify: the view by setting a new sequencer configuration
  v.seq_config = seq_config;

  // write: the proposed new view
  auto data = v.serialize();
  int ret = log_->backend->ProposeView(log_->hoid, next_epoch, data);
  if (!ret || ret == -ESPIPE) {
    update_current_view(v.epoch());
    return 0;
  }

  return ret;
}

// no deduplication is performed here, but this is only triggered by the thread
// that successfully creates a new stripe, of which there should just be one per
// stripe. later if/when we try to optimize for the rare case of the stripe
// creator crashing before finishing initialization, we _might_ run into a case
// where we want to deduplicate the stripe init jobs.
void Striper::async_init_stripe(uint64_t position)
{
  std::lock_guard<std::mutex> lk(lock_);
  stripe_init_pos_.push_back(position);
  stripe_init_cond_.notify_one();
}

void Striper::stripe_init_entry_()
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
    auto stripe = v->object_map.map_stripe(position);
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
      log_->backend->Seal(oid, v->epoch());
    }
  }
}

void Striper::expander_entry_()
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
    const auto mapping = v->object_map.map(position);
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

void Striper::async_expand_view(uint64_t position)
{
  std::unique_lock<std::mutex> lk(lock_);
  if (!expand_pos_ || position > *expand_pos_) {
    expand_pos_ = position;
    expander_cond_.notify_one();
  }
}

void Striper::refresh_entry_()
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
    int ret = log_->backend->ReadViews(log_->hoid, epoch,
        log_->options.max_refresh_views_read, &views);
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

    zlog_proto::View view_src;
    if (!view_src.ParseFromString(it->second)) {
      assert(0);
      exit(1);
    }

    auto new_view = std::make_shared<View>(log_->prefix, it->first, view_src);

    if (new_view->seq_config) {
      if (new_view->seq_config->secret == secret_) { // we should be the active seq
        if (new_view->seq_config->epoch == it->first) {
          new_view->seq = std::make_shared<Sequencer>(it->first,
              new_view->seq_config->position);
        } else {
          assert(new_view->seq_config->epoch < it->first);
          std::lock_guard<std::mutex> lk(lock_);
          assert(view_->seq);
          assert(view_->seq_config);
          assert(view_->seq_config->epoch == new_view->seq_config->epoch);
          assert(view_->seq->epoch() == view_->seq_config->epoch);
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

void Striper::update_current_view(const uint64_t epoch)
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

std::string View::create_initial()
{
  std::string blob;
  zlog_proto::View view;
  view.set_min_valid_position(0);
  if (!view.SerializeToString(&blob)) {
    assert(0);
    exit(1);
  }
  return blob;
}

std::string View::serialize() const
{
  zlog_proto::View view;

  for (const auto& stripe : object_map.stripes()) {
    auto pb_stripe = view.add_stripes();
    pb_stripe->set_id(stripe.second.id());
    pb_stripe->set_width(stripe.second.width());
    pb_stripe->set_min_position(stripe.first);
    pb_stripe->set_max_position(stripe.second.max_position());
  }
  view.set_next_stripe_id(object_map.next_stripe_id());

  if (seq_config) {
    auto seq = view.mutable_seq();
    seq->set_epoch(seq_config->epoch);
    seq->set_secret(seq_config->secret);
    seq->set_position(seq_config->position);
  }

  view.set_min_valid_position(min_valid_position);

  std::string blob;
  if (!view.SerializeToString(&blob)) {
    std::cerr << "invalid proto" << std::endl << std::flush;
    assert(0);
    exit(1);
    return "";
  }

  return blob;
}

View::View(const std::string& prefix, uint64_t epoch,
    const zlog_proto::View& view) :
  epoch_(epoch)
{
  std::map<uint64_t, Stripe> stripes;
  for (auto stripe : view.stripes()) {
    auto res = stripes.emplace(stripe.min_position(),
        Stripe(prefix, stripe.id(), stripe.width(), stripe.max_position()));
    assert(res.second);
  }

  if (!stripes.empty()) {
    std::set<uint64_t> ids;
    auto it = stripes.cbegin();
    auto it2 = std::next(it);
    for (; it != stripes.cend(); it++) {
      assert(it->first <= it->second.max_position());
      assert(it->second.width() > 0);
      auto res = ids.emplace(it->second.id());
      assert(res.second);
      if (it2 != stripes.cend()) {
        assert(it->second.max_position() < it2->first);
	it2++;
      }
    }
    assert(ids.find(view.next_stripe_id()) == ids.end());
  }

  object_map = ObjectMap(view.next_stripe_id(), stripes);

  if (view.has_seq()) {
    auto seq = view.seq();
    SequencerConfig conf;
    conf.epoch = seq.epoch();
    conf.secret = seq.secret();
    conf.position = seq.position();
    seq_config = conf;
    assert(seq_config->epoch > 0);
    assert(!seq_config->secret.empty());
  }

  min_valid_position = view.min_valid_position();
}

}
