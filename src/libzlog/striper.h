#pragma once
#include <atomic>
#include <map>
#include <mutex>
#include <thread>
#include <sstream>
#include <list>
#include <condition_variable>
#include <boost/optional.hpp>
#include "libzlog/zlog.pb.h"

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
  //
  //

// remove prefix from multistripe/stripe and pass around log reference when
// generating object names?
//
// document locking around data structures like objectmap/stripe. i think its as
// simple as noting that all operations are on copies of the view.
//
// should MultiStripe have its own serializatio method?
//
// TODO check assumptions about disjoint ranges in objectmap/multistripe
//
// record any notes about how to change the stripe configuration
// const auto min_position = empty_map ? 0 : (it->second.max_position() + 1);
// const auto max_position = min_position + num_stripe_entries - 1;

namespace zlog_proto {
  class View;
}

namespace zlog {

class LogImpl;
struct Options;

class Sequencer {
 public:
  explicit Sequencer(uint64_t epoch, uint64_t position) :
    epoch_(epoch),
    position_(position)
  {}

  uint64_t check_tail(bool next) {
    if (next) {
      return position_.fetch_add(1);
    } else {
      return position_.load();
    }
  }

  uint64_t epoch() const {
    return epoch_;
  }

 private:
  const uint64_t epoch_;
  std::atomic<uint64_t> position_;
};

class Stripe {
 public:
  Stripe(const std::string& prefix,
      uint64_t stripe_id,
      uint32_t width,
      uint64_t min_position,
      uint64_t max_position) :
    prefix_(prefix),
    stripe_id_(stripe_id),
    width_(width),
    min_position_(min_position),
    max_position_(max_position),
    oids_(make_oids())
  {}

  uint64_t min_position() const {
    return min_position_;
  }

  uint64_t max_position() const {
    return max_position_;
  }

  uint32_t width() const {
    return width_;
  }

  const std::vector<std::string>& oids() const {
    return oids_;
  }

  static std::string make_oid(const std::string& prefix,
      uint64_t stripe_id, uint32_t width, uint64_t position);

 private:
  static std::string make_oid(const std::string& prefix,
      uint64_t stripe_id, uint32_t index);

  std::vector<std::string> make_oids();

  const std::string prefix_;
  const uint64_t stripe_id_;
  const uint32_t width_;
  const uint64_t min_position_;
  const uint64_t max_position_;
  const std::vector<std::string> oids_;
};

class MultiStripe {
 public:
  MultiStripe(const std::string& prefix,
      uint64_t base_id,
      uint32_t width,
      uint32_t slots,
      uint64_t min_position,
      uint64_t instances,
      uint64_t max_position) :
    prefix_(prefix),
    base_id_(base_id),
    width_(width),
    slots_(slots),
    min_position_(min_position),
    instances_(instances),
    max_position_(max_position)
  {
    assert(!prefix_.empty());
    assert(base_id_ >= 0);
    assert(width_ > 0);
    assert(slots_ > 0);
    assert(min_position_ >= 0);
    assert(instances_ > 0);
    assert(max_position_ > 0);
  }

  std::string map(uint64_t stripe_id, uint64_t position) const {
    return Stripe::make_oid(prefix_, stripe_id, width_, position);
  }

  uint64_t base_id() const {
    return base_id_;
  }

  uint64_t max_stripe_id() const {
    return base_id_ + instances_ - 1;
  }

  uint64_t max_position() const {
    return max_position_;
  }

  uint32_t width() const {
    return width_;
  }

  uint32_t slots() const {
    return slots_;
  }

  uint32_t instances() const {
    return instances_;
  }

  Stripe stripe_by_id(uint64_t stripe_id) const {
    assert(base_id() <= stripe_id);
    assert(stripe_id <= max_stripe_id());
    const uint64_t stripe_offset = stripe_id - base_id();
    const uint64_t entries_per_stripe = (uint64_t)width_ * slots_;
    const uint64_t min_pos = min_position_ + (stripe_offset * entries_per_stripe);
    const uint64_t max_pos = min_pos + entries_per_stripe - 1;
    assert(stripe_offset < instances_);
    assert(entries_per_stripe > 0);
    assert(min_pos >= min_position_);
    assert(max_pos <= max_position_);
    return Stripe(
        prefix_,
        stripe_id,
        width_,
        min_pos,
        max_pos);
  }

  void extend() {
    instances_++;
    max_position_ += (uint64_t)width_ * slots_;
  }

 private:
  const std::string prefix_;
  const uint64_t base_id_;
  const uint32_t width_;
  const uint32_t slots_;
  const uint64_t min_position_;
  uint64_t instances_;
  uint64_t max_position_;
};

class ObjectMap {
 public:
  ObjectMap() :
    next_stripe_id_(0)
  {}

  // TODO we should be able to deduce the next stripe id, right?
  ObjectMap(uint64_t next_stripe_id,
      const std::map<uint64_t, MultiStripe>& stripes) :
    next_stripe_id_(next_stripe_id),
    stripes_by_pos_(stripes)
  {
    for (auto it = stripes_by_pos_.cbegin(); it != stripes_by_pos_.cend(); it++) {
      stripes_by_id_.emplace(it->second.base_id(), it);
    }
  }

 public:
  // returns the object name that maps the position, if it exists. the second
  // element is true iff the position maps to the last stripe in the object map.
  std::pair<boost::optional<std::string>, bool> map(uint64_t position) const;

  // expand the mapping to include the given position. true is returned when the
  // mapping changed, and false if the position is already mapped.
  bool expand_mapping(const std::string& prefix, const uint64_t position,
      const Options& options);

  // returns the stripe with the given stripe id.
  Stripe stripe_by_id(uint64_t stripe_id) const;

  // returns the id of the next stripe in the object map.
  uint64_t next_stripe_id() const {
    return next_stripe_id_;
  }

  // returns the maximum position mapped by the object map.
  uint64_t max_position() const;

  // returns true if the object map contains no stripes.
  bool empty() const {
    return stripes_by_pos_.empty();
  }

  // returns the number of stripes.
  uint64_t num_stripes() const {
    return next_stripe_id_;
  }

  const std::map<uint64_t, MultiStripe>& multi_stripes() const {
    return stripes_by_pos_;
  }

  // TODO iterate over these stripes rather than creating a large data
  // structure with all the stripes materialized.
  boost::optional<std::vector<std::pair<std::string, bool>>> map_to(
      uint64_t position) const;

  // return the stripe that maps the position.
  boost::optional<Stripe> map_stripe(uint64_t position) const;

 private:
  uint64_t next_stripe_id_;
  std::map<uint64_t, MultiStripe> stripes_by_pos_;
  std::map<uint64_t, std::map<uint64_t, MultiStripe>::const_iterator> stripes_by_id_;
};

struct SequencerConfig {
  uint64_t epoch;
  std::string secret;
  uint64_t position;
};

// separate configuration from initialization. for instance, after deserializing
// a protobuf into its view, don't immediately create and connect the sequencer.
//
// TODO: separate view with epoch from view without it
class View {
 public:
  View() :
    epoch_(0)
  {}

  View(const std::string& prefix, uint64_t epoch,
      const zlog_proto::View& view);

  // construct the initial view for a new log.
  static std::string create_initial(const Options& options);

  uint64_t epoch() const {
    return epoch_;
  }

  std::string serialize() const;

  ObjectMap object_map;
  boost::optional<SequencerConfig> seq_config;
  uint64_t min_valid_position;

  std::shared_ptr<Sequencer> seq;

 private:
  const uint64_t epoch_;
};

class Striper {
 public:
  Striper(LogImpl *log, const std::string& secret);

  ~Striper();

  void shutdown();

  std::shared_ptr<const View> view() const;

  boost::optional<std::string> map(const std::shared_ptr<const View>& view,
      uint64_t position);

  boost::optional<std::vector<std::pair<std::string, bool>>> map_to(
      const std::shared_ptr<const View>& view,
      uint64_t position);

  // proposes a new log view as a copy of the current view that has been
  // expanded to map the position. no proposal is made if the current view maps
  // the position. if a proposal is made this method doesn't return until the
  // new view (or a newer view) is made active. on success, callers should
  // verify that the position has been mapped, and retry if it is still missing.
  int try_expand_view(uint64_t position);
  void async_expand_view(uint64_t position);

  // schedule initialization of the stripe that maps the position.
  void async_init_stripe(uint64_t position);

  // wait until a view that is newer than the given epoch is read and made
  // active. this is typically used when a backend method (e.g. read, write)
  // returns -ESPIPE indicating that I/O was tagged with an out-of-date epoch,
  // and the caller should retrieve the latest view.
  void update_current_view(uint64_t epoch);

  // proposes a new view with this log instance configured as the active
  // sequencer. this method waits until the propsoed view (or a newer view) is
  // made active. on success, caller should check the sequencer of the current
  // view and propose again if necessary.
  int propose_sequencer();

  // updates the current view's minimum valid position to be _at least_
  // position. note that this also may expand the range of invalid entries. this
  // method is used for trimming the log in the range [0, position-1]. this
  // method will be return success immediately if the proposed position is <=
  // the current minimum.
  int advance_min_valid_position(uint64_t position);

 private:
  mutable std::mutex lock_;
  bool shutdown_;
  LogImpl * const log_;
  const std::string secret_;

 private:
  // seals the given stripe with the given epoch. on success, *pempty will be
  // set to true if the stripe is empty (no positions have been written, filled,
  // etc...), and if the stripe is non-empty, *pposition will be set to the
  // maximum position written. otherwise it is left unmodified.
  int seal_stripe(const Stripe& stripe, uint64_t epoch,
      uint64_t *pposition, bool *pempty) const;

  std::shared_ptr<const View> view_;

 private:
  struct RefreshWaiter {
    explicit RefreshWaiter(uint64_t epoch) :
      done(false),
      epoch(epoch)
    {}

    bool done;
    const uint64_t epoch;
    std::condition_variable cond;
  };

  // log replay (read and activate views)
  void refresh_entry_();
  std::list<RefreshWaiter*> refresh_waiters_;
  std::condition_variable refresh_cond_;
  std::thread refresh_thread_;

  // async view expansion
  boost::optional<uint64_t> expand_pos_;
  std::condition_variable expander_cond_;
  void expander_entry_();
  std::thread expander_thread_;

  // async stripe initilization
  std::list<uint64_t> stripe_init_pos_;
  std::condition_variable stripe_init_cond_;
  void stripe_init_entry_();
  std::thread stripe_init_thread_;
};

}
