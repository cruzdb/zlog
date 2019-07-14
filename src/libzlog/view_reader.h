#pragma once
#include <condition_variable>
#include <list>
#include <memory>
#include <mutex>
#include <thread>
#include "libzlog/view.h"
#include "include/zlog/options.h"

namespace zlog {

class Backend;

class ViewReader final {
 public:
  ViewReader(
    const std::shared_ptr<Backend> backend,
    const std::string& hoid,
    const std::string& prefix,
    const std::string& secret,
    const Options& options);

  ViewReader(const ViewReader& other) = delete;
  ViewReader(ViewReader&& other) = delete;
  ViewReader& operator=(const ViewReader& other) = delete;
  ViewReader& operator=(ViewReader&& other) = delete;

  void shutdown();

  ~ViewReader();

 public:
  // return the current view. this will return nullptr until the first view is
  // installed (e.g. via `refresh_view`). after the first view is installed,
  // this method will always return a valid view.
  std::shared_ptr<const VersionedView> view() const;

  // ensure that the latest view is being used.
  void refresh_view();

  // wait until a view that is newer than the given epoch is read and made
  // active. this is typically used when a backend method (e.g. read, write)
  // returns -ESPIPE indicating that I/O was tagged with an out-of-date epoch,
  // and the caller should retrieve the latest view.
  void update_current_view(uint64_t epoch);

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
  const std::shared_ptr<Backend> backend_;
  const std::string hoid_;
  const std::string prefix_;
  const std::string secret_;
  const Options options_;

  std::shared_ptr<const VersionedView> view_;

  void refresh_entry_();
  std::list<RefreshWaiter*> refresh_waiters_;
  std::condition_variable refresh_cond_;
  std::thread refresh_thread_;
};

}
