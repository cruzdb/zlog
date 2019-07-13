#pragma once
#include <mutex>
#include <thread>
#include <list>
#include <condition_variable>
#include <boost/optional.hpp>
#include "include/zlog/options.h"
#include "stripe.h"
#include "view.h"

// TODO
//  - ViewReader - log replay
//  - ViewManager - Striper

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

namespace zlog {

class Backend;

class LogImpl;

class Striper {
 public:
  // Striper factory that initializes the instance with the latest view.
  static std::unique_ptr<Striper> open(
    const std::shared_ptr<Backend> backend,
    const std::string& hoid,
    const std::string& prefix,
    const std::string& secret,
    const Options& options);

  Striper(const Striper& other) = delete;
  Striper(Striper&& other) = delete;
  Striper& operator=(const Striper& other) = delete;
  Striper& operator=(Striper&& other) = delete;

  ~Striper();

 public:
  void shutdown();

  std::shared_ptr<const VersionedView> view() const;

  boost::optional<std::string> map(const std::shared_ptr<const View>& view,
      uint64_t position);

  boost::optional<std::vector<std::pair<std::string, bool>>> map_to(
      const std::shared_ptr<const View>& view, const uint64_t position,
      uint64_t& stripe_id, bool& done) const;

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
  Striper(std::shared_ptr<Backend> backend,
    std::unique_ptr<VersionedView> view,
    const std::string& hoid,
    const std::string& prefix,
    const std::string& secret,
    const Options& options);

 private:
  mutable std::mutex lock_;
  bool shutdown_;
  const std::shared_ptr<Backend> backend_;
  const std::string hoid_;
  const std::string prefix_;
  const std::string secret_;
  const Options options_;

 private:
  // seals the given stripe with the given epoch. on success, *pempty will be
  // set to true if the stripe is empty (no positions have been written, filled,
  // etc...), and if the stripe is non-empty, *pposition will be set to the
  // maximum position written. otherwise it is left unmodified.
  int seal_stripe(const Stripe& stripe, uint64_t epoch,
      uint64_t *pposition, bool *pempty) const;

  // the current view. any view itself is immutable, but as new views are
  // created and discovered the current view is replaced with newer views.
  std::shared_ptr<const VersionedView> view_;

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
