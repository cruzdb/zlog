#pragma once
#include <condition_variable>
#include <list>
#include <memory>
#include <mutex>
#include <thread>
#include "libzlog/view.h"
#include "include/zlog/options.h"

namespace zlog {

class LogBackend;

/**
 * ViewReader provides access to the latest log view.
 *
 * ViewReader reads and instantiates the log's latest view from the storage
 * backend, and notifies any threads that are waiting on a view with a minimum
 * epoch to become active.
 */
class ViewReader final {
 public:
  ViewReader(
    const std::shared_ptr<LogBackend> backend,
    const Options& options);

  ViewReader(const ViewReader& other) = delete;
  ViewReader(ViewReader&& other) = delete;
  ViewReader& operator=(const ViewReader& other) = delete;
  ViewReader& operator=(ViewReader&& other) = delete;

  void shutdown();

  ~ViewReader();

 public:
  // Return the current view. Until a view is set, nullptr will be returned.
  // After a view is set, a valid view will always be returned. The intended use
  // of these semantics is:
  //
  //   1) Create a ViewReader
  //   2) Call `refresh_view()`
  //   3) If `view()` returns a view, then the ViewReader can be used by a
  //      consumer that assumes `view()` always returns a valid view.
  std::shared_ptr<const VersionedView> view() const;

  // Ensure that the current view is up to date.
  void refresh_view();

  // wait until a view that is newer than the given epoch is read and made
  // active. this is typically used when a backend method (e.g. read, write)
  // returns -ESPIPE indicating that I/O was tagged with an out-of-date epoch,
  // and the caller should retrieve the latest view.
  void wait_for_newer_view(uint64_t epoch);

 private:
  std::unique_ptr<VersionedView> get_latest_view() const;

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

 private:
  mutable std::mutex lock_;
  bool shutdown_;
  const std::shared_ptr<LogBackend> backend_;
  const Options options_;

  std::shared_ptr<const VersionedView> view_;

  void refresh_entry_();
  std::list<RefreshWaiter*> refresh_waiters_;
  std::condition_variable refresh_cond_;
  std::thread refresh_thread_;
};

}
