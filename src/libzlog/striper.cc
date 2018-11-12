#include "striper.h"
#include "proto/zlog.pb.h"
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

boost::optional<std::string> ObjectMap::map(const uint64_t position) const
{
  if (!stripes_.empty()) {
    auto it = stripes_.upper_bound(position);
    it = std::prev(it);
    assert(it->first <= position);
    if (position <= it->second.max_position()) {
      auto oid = it->second.map(position);
      return oid;
    }
  }
  return boost::none;
}

bool ObjectMap::expand_mapping(const std::string& prefix,
    const uint64_t position)
{
  if (map(position)) {
    return false;
  }

  uint32_t width = 10;
  uint32_t object_slots = 5;

  const uint64_t stripe_slots = (uint64_t)width * object_slots;
  assert(stripe_slots > 0);

  do {
    const auto it = stripes_.crbegin();
    const auto empty = it == stripes_.crend();
    const auto min_position = empty ? 0 : (it->second.max_position() + 1);
    const auto max_position = min_position + stripe_slots - 1;
    const auto stripe_id = next_stripe_id_++;
    stripes_.emplace(min_position,
        Stripe{prefix, stripe_id, width, max_position});
  } while (!map(position));

  return true;
}

Striper::Striper(LogImpl *log, const std::string& secret) :
  shutdown_(false),
  log_(log),
  secret_(secret),
  view_(std::make_shared<const View>()),
  refresh_thread_(std::thread(&Striper::refresh_entry_, this))
{
}

Striper::~Striper()
{
  {
    std::lock_guard<std::mutex> lk(lock_);
    assert(shutdown_);
    assert(refresh_waiters_.empty());
  }
  assert(!refresh_thread_.joinable());
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
  refresh_thread_.join();
}

int Striper::try_expand_view(const uint64_t position)
{
  // read: the view into a mutable copy
  auto v = *view();
  const auto next_epoch = v.epoch() + 1;

  // modify: the object map to contain the position
  auto changed = v.object_map.expand_mapping(log_->prefix, position);
  if (!changed) {
    return 0;
  }

  // write: the serialized view as a new epoch view
  auto data = v.serialize();
  int ret = log_->backend->ProposeView(log_->hoid, next_epoch, data);
  if (!ret || ret == -ESPIPE) {
    update_current_view(v.epoch());
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

void Striper::refresh_entry_()
{
  while (true) {
    uint64_t current_epoch;

    {
      std::unique_lock<std::mutex> lk(lock_);

      refresh_cond_.wait(lk, [&] {
        return !refresh_waiters_.empty() || shutdown_;
      });

      if (shutdown_)
        break;

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
  RefreshWaiter waiter(epoch);
  std::unique_lock<std::mutex> lk(lock_);
  refresh_waiters_.emplace_back(&waiter);
  refresh_cond_.notify_one();
  waiter.cond.wait(lk, [&waiter] { return waiter.done; });
}

std::string View::create_initial()
{
  std::string blob;
  zlog_proto::View view;
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
      }
      it2++;
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
}

}
