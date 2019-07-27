#pragma once
#include <mutex>
#include <thread>
#include <list>
#include <condition_variable>
#include <boost/optional.hpp>
#include "include/zlog/options.h"
#include "libzlog/view_reader.h"
#include "stripe.h"
#include "libzlog/view.h"

namespace zlog {

class LogBackend;
class LogImpl;

class ViewManager final {
 public:
  ViewManager(const Options& options,
      std::shared_ptr<LogBackend> backend,
    std::unique_ptr<ViewReader> view_reader);

  ViewManager(const ViewManager& other) = delete;
  ViewManager(ViewManager&& other) = delete;
  ViewManager& operator=(const ViewManager& other) = delete;
  ViewManager& operator=(ViewManager&& other) = delete;

  void shutdown();

  ~ViewManager();

 public:
  std::shared_ptr<const VersionedView> view() const {
    return view_reader_->view();
  }

  void update_current_view(uint64_t epoch, bool wakeup = false) {
    return view_reader_->wait_for_newer_view(epoch, wakeup);
  }

 public:
  // TODO versioned view?
  boost::optional<std::string> map(const std::shared_ptr<const View>& view,
      uint64_t position);

  boost::optional<std::vector<std::pair<std::string, bool>>> map_to(
      const std::shared_ptr<const View>& view, const uint64_t position,
      uint64_t& stripe_id, bool& done) const;

  // schedule initialization of the stripe that maps the position.
  void async_init_stripe(uint64_t position);

  // updates the current view's minimum valid position to be _at least_
  // position. note that this also may expand the range of invalid entries. this
  // method is used for trimming the log in the range [0, position-1]. this
  // method will be return success immediately if the proposed position is <=
  // the current minimum.
  int advance_min_valid_position(uint64_t position);

 public:
  // propose a view with a new sequencer. when success (0) is returned the
  // proposal was successful, but the caller should still verify that the
  // sequencer is configured as expected.
  int propose_sequencer();

  // proposes a new log view as a copy of the current view that has been
  // expanded to map the position. no proposal is made if the current view maps
  // the position. if a proposal is made this method doesn't return until the
  // new view (or a newer view) is made active. on success, callers should
  // verify that the position has been mapped, and retry if it is still missing.
  int try_expand_view(uint64_t position);
  void async_expand_view(uint64_t position);

 private:
  mutable std::mutex lock_;
  bool shutdown_;
  const std::shared_ptr<LogBackend> backend_;
  const Options options_;

  const std::unique_ptr<ViewReader> view_reader_;

 private:
  // seals the given stripe with the given epoch. on success, *pempty will be
  // set to true if the stripe is empty (no positions have been written, filled,
  // etc...). if the stripe is non-empty, *pposition will be set to the maximum
  // position written. otherwise it is left unmodified.
  int seal_stripe(const Stripe& stripe, uint64_t epoch,
      uint64_t *pposition, bool *pempty) const;

 private:
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
