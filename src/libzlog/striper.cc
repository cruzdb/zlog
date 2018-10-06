#include "striper.h"
#include "proto/zlog.pb.h"
#include "log_impl.h"
#include <iterator>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include "libzlog/fakeseqr.h"

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

bool ObjectMap::ensure_mapping(const std::string& prefix,
    const uint64_t position)
{
  if (map(position))
    return false;

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

void Striper::shutdown()
{
  {
    std::lock_guard<std::mutex> lk(lock_);
    shutdown_ = true;
  }
  cond_.notify_one();
  refresh_thread_.join();
}

int Striper::ensure_mapping(const uint64_t position)
{
  // read / copy
  auto v = *view();
  const auto next_epoch = v.epoch() + 1;

  // modify
  auto changed = v.object_map.ensure_mapping(log_->prefix, position);
  if (!changed)
    return 0;

  // write
  auto data = v.serialize();
  int ret = log_->backend->ProposeView(log_->hoid, next_epoch, data);
  if (!ret || ret == -ESPIPE) {
    //  - if success or bad-epoch, refresh, return success
    refresh(v.epoch());
    return 0;
  }

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
  uint64_t stripe_max_pos = 0;

  for (auto& oid : oids) {
    bool empty;
    uint64_t max_pos;
    int ret = log_->backend->MaxPos(oid, epoch, &max_pos, &empty);
    if (ret < 0) {
      return ret;
    }

    if (empty)
      continue;

    stripe_empty = false;
    stripe_max_pos = std::max(stripe_max_pos, max_pos);
  }

  if (pempty)
    *pempty = stripe_empty;

  if (pposition) {
    if (!stripe_empty)
      *pposition = stripe_max_pos;
  }

  return 0;
}

std::string Striper::make_cookie()
{
  auto uuid = boost::uuids::random_generator()();
  auto hostname = boost::asio::ip::host_name();

  std::stringstream ss;
  ss << uuid << "." << hostname;
  return ss.str();
}

int Striper::propose_sequencer(const std::shared_ptr<const View>& view,
    const Options& options)
{
  auto v = *view;
  const auto next_epoch = v.epoch() + 1;

  bool empty = true;
  uint64_t max_pos;

  // the maximum position is contained in the first non-empty stripe scanning in
  // reverse, beginning with the stripe that maps the maximum possible position
  // for the current view.
  const auto stripes = v.object_map.stripes();
  auto it = stripes.crbegin();
  for (; it != stripes.crend(); it++) {
    auto& stripe = it->second;
    int ret = seal_stripe(stripe, next_epoch, &max_pos, &empty);
    if (ret < 0) {
      return ret;
    }

    if (empty)
      continue;

    it++;
    break;
  }

  if (empty) {
    assert(it == stripes.crend());
  }

  // now seal all of the other stripes. this is not so the max remains valid,
  // but so that clients speaking with other sequencers that might still be
  // active are forced to grab a new view and see the new sequencer.
  for (; it != stripes.crend(); it++) {
    auto& stripe = it->second;
    int ret = seal_stripe(stripe, next_epoch, nullptr, nullptr);
    if (ret < 0) {
      return ret;
    }
  }

  assert(options.seq_host.empty());
  assert(options.seq_port.empty());

  SequencerConfig seq_config;
  seq_config.init_position = empty ? 0 : (max_pos + 1);

  seq_config.cookie = cookie_;

  // this is the epoch at which the new seq takes affect. this controls the
  // validitiy of init_position since the seq info is copied into new views.
  // maybe we could solve this issue by clearing init position on cpoy, or
  // breaking out into different data structures?
  seq_config.epoch = next_epoch;

  v.seq_config = seq_config;

  // propose the same view unmodified. finding the maximum position doesn't
  // require changing the view, but rather only ensuring that no in-flight
  // writes invalidate the result which is accomplished by sealing the stripes
  // queried and aborting the process if the view changed during the process.
  auto data = v.serialize();
  int ret = log_->backend->ProposeView(log_->hoid, next_epoch, data);
  if (ret) {
    return ret;
  }

  return 0;
}

void Striper::refresh_entry_()
{
  console->info("starting view refresh thread");

  while (true) {
    uint64_t current_epoch;

    {
      std::unique_lock<std::mutex> lk(lock_);
      cond_.wait(lk, [&] { return !waiters_.empty() || shutdown_; });

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
    int ret = log_->backend->ReadViews(log_->hoid, epoch, views);
    if (ret) {
      std::cerr << "read views error " << ret << std::endl;
      continue;
    }

    // no newer views were found. notify the waiters.
    if (views.empty()) {
      std::list<RefreshWaiter*> waiters;
      {
        std::lock_guard<std::mutex> lk(lock_);
        waiters.swap(waiters_);
      }
      for (auto it = waiters.begin(); it != waiters.end();) {
        const auto waiter = *it;
        if (current_epoch > waiter->epoch) {
          waiter->done = true;
          waiter->cond.notify_one();
          console->info("waking up waiter {}", waiter->epoch);
          it = waiters.erase(it);
        } else {
          it++;
        }
      }
      if (!waiters.empty()) {
        std::lock_guard<std::mutex> lk(lock_);
        waiters_.splice(waiters_.begin(), waiters);
      }
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

    const auto it = views.crbegin();
    assert(it != views.crend());

    zlog_proto::View view_src;
    if (!view_src.ParseFromString(it->second)) {
      assert(0);
      exit(1);
    }

    auto new_view = std::make_shared<View>(log_->prefix, it->first, view_src);

    if (new_view->seq_config.cookie == cookie_) {
      if (new_view->seq_config.epoch == it->first) {
        new_view->seq = std::make_shared<FakeSeqrClient>(log_->backend->meta(),
            log_->name, new_view->seq_config.init_position, 0);
      } else {
        std::cout << "skipping new seq creation" << std::endl;
      }
    } else {
      new_view->seq = nullptr;
    }

    console->info("activate view {}", it->first);

    std::lock_guard<std::mutex> lk(lock_);
    view_ = std::move(new_view);
  }
}

void Striper::refresh(const uint64_t epoch)
{
  RefreshWaiter waiter(epoch);
  std::unique_lock<std::mutex> lk(lock_);
  waiters_.emplace_back(&waiter);
  cond_.notify_one();
  waiter.cond.wait(lk, [&waiter] { return waiter.done; });
}

////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

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

  auto seq = view.mutable_seq();
  seq->set_host(seq_config.host);
  seq->set_port(seq_config.port);
  seq->set_cookie(seq_config.cookie);
  seq->set_init_position(seq_config.init_position);
  seq->set_epoch(seq_config.epoch);

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

  object_map = ObjectMap(view.next_stripe_id(), stripes);

  seq_config.host = view.seq().host();
  seq_config.port = view.seq().port();
  seq_config.cookie = view.seq().cookie();
  seq_config.init_position = view.seq().init_position();
  seq_config.epoch = view.seq().epoch();
}

}
