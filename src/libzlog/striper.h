#pragma once
#include <atomic>
#include <map>
#include <mutex>
#include <thread>
#include <sstream>
#include <list>
#include <condition_variable>
#include <boost/optional.hpp>
#include "proto/zlog.pb.h"

  // don't want to expand mappings on an empty object map (like the zero state)
  // need to figure that out. as it stands map would send caller to
  // ensure_mapping which woudl expand a objectmap with no stripes. it's a weird
  // edge case we should consider.
  //
  // maybe having view allowed to be null is ok?
  // wrap calls to view and check for epoch = 0?
  //
  //
  // the zero value of these structures might make initialization eassy too.
  // like stripe id starting at 0 makes sense. for ensure mapping it would just
  // add using default width, then correctly propose epoch 1.
  //
  // i like that zero value version. we could say ok if you don't want some
  // default width to be used then don't call append or whatever right after
  // making the log / log instance. instead, call something like wait_for_init.
  //
  // i think the other really good option is to just define object map to always
  // be initialized from a proto view from the log.


namespace zlog_proto {
  class View;
}

namespace zlog {

class LogImpl;
class Options;

class Sequencer {
 public:
  explicit Sequencer(uint64_t position) :
    position_(position)
  {}

  uint64_t check_tail(bool next) {
    if (next) {
      return position_.fetch_add(1);
    } else {
      return position_.load();
    }
  }

 private:
  std::atomic<uint64_t> position_;
};

class Stripe {
 public:
  Stripe(const std::string& prefix, uint64_t id,
      uint32_t width, uint64_t max_position) :
    id_(id),
    max_position_(max_position),
    oids_(make_oids(prefix, id_, width))
  {
    assert(!oids_.empty());
  }

  std::string map(uint64_t position) const {
    const auto index = position % oids_.size();
    return oids_[index];
  }

  uint64_t id() const {
    return id_;
  }

  uint64_t max_position() const {
    return max_position_;
  }

  uint32_t width() const {
    return oids_.size();
  }

  const std::vector<std::string>& oids() const {
    return oids_;
  }

 private:
  static std::vector<std::string> make_oids(
      const std::string& prefix, uint64_t id, uint32_t width);

  const uint64_t id_;
  uint64_t max_position_;
  const std::vector<std::string> oids_;
};

class ObjectMap {
 public:
  ObjectMap() :
    next_stripe_id_(0)
  {}

  ObjectMap(uint64_t next_stripe_id,
      std::map<uint64_t, Stripe>& stripes) :
    next_stripe_id_(next_stripe_id),
    stripes_(stripes)
  {}

 public:
  boost::optional<std::string> map(uint64_t position) const;
  bool ensure_mapping(const std::string& prefix, uint64_t position);

  const std::map<uint64_t, Stripe>& stripes() const {
    return stripes_;
  }

  uint64_t next_stripe_id() const {
    return next_stripe_id_;
  }

 private:
  uint64_t next_stripe_id_;
  std::map<uint64_t, Stripe> stripes_;
};

struct SequencerConfig {
  std::string cookie;
  uint64_t init_position;
  uint64_t epoch;
};

// separate configuration from initialization. for instance, after deserializing
// a protobuf into its view, don't immediately create and connect the sequencer.
class View {
 public:
  View() :
    epoch_(0)
  {}

  View(const std::string& prefix, uint64_t epoch,
      const zlog_proto::View& view);

  static std::string create_initial();

  uint64_t epoch() const {
    return epoch_;
  }

  std::string serialize() const;

  ObjectMap object_map;
  SequencerConfig seq_config;

  std::shared_ptr<Sequencer> seq;

 private:
  const uint64_t epoch_;
};

class Striper {
 public:
  Striper(LogImpl *log) :
    shutdown_(false),
    log_(log),
    view_(std::make_shared<const View>()),
    cookie_(make_cookie()),
    refresh_thread_(std::thread(&Striper::refresh_entry_, this))
  {}

  std::shared_ptr<const View> view() const {
    assert(view_);
    return view_;
  }

  int ensure_mapping(uint64_t position);

  void refresh(uint64_t epoch = 0);

  int propose_sequencer(const std::shared_ptr<const View>& view,
      const Options& options);

  void shutdown();

 private:
  // seals the stripe at the given epoch. *pempty will be set to true if the
  // stripe is empty. *pposition is set to the maximum position written in the
  // stripe, and is only defined when the stripe is non-empty.
  int seal_stripe(const Stripe& stripe, uint64_t epoch,
      uint64_t *pposition, bool *pempty) const;

  static std::string make_cookie();

  mutable std::mutex lock_;
  bool shutdown_;
  LogImpl *log_;
  std::shared_ptr<const View> view_;

  const std::string cookie_;

  struct RefreshWaiter {
    explicit RefreshWaiter(uint64_t epoch) :
      done(false),
      epoch(epoch)
    {}

    bool done;
    const uint64_t epoch;
    std::condition_variable cond;
  };

  void refresh_entry_();
  std::list<RefreshWaiter*> waiters_;
  std::condition_variable cond_;
  std::thread refresh_thread_;
};

}
