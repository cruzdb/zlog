#pragma once
#include <condition_variable>
#include <list>
#include <mutex>
#include <thread>

#include "include/zlog/log.h"
#include "include/zlog/statistics.h"
#include "libseq/libseqr.h"
#include "include/zlog/backend.h"
#include "log_backend.h"
#include "view_manager.h"

#define DEFAULT_STRIPE_SIZE 100

namespace zlog {

typedef Backend *(*backend_allocate_t)(void);
typedef void (*backend_release_t)(Backend*);

class PositionOp;

class LogImpl : public Log {
 public:
  LogImpl(const LogImpl&) = delete;
  LogImpl(const LogImpl&&) = delete;
  LogImpl& operator=(const LogImpl&) = delete;
  LogImpl& operator=(const LogImpl&&) = delete;

  LogImpl(std::shared_ptr<LogBackend> backend,
      const std::string& name,
      std::unique_ptr<ViewManager> view_mgr,
      const Options& opts);

  ~LogImpl();

 public:
  int CheckTail(uint64_t *pposition) override;
  int CheckTail(uint64_t *pposition, bool increment);

 public:
  int Read(uint64_t position, std::string *data) override;
  int Append(const std::string& data, uint64_t *pposition) override;
  int Fill(uint64_t position) override;
  int Trim(uint64_t position) override;

 public:
  void finisher_entry_();
  std::vector<std::thread> finishers_;
  std::condition_variable finishers_cond_;
  std::list<std::unique_ptr<PositionOp>> pending_ops_;
  void queue_op(std::unique_ptr<PositionOp> op);
  void try_op(PositionOp& op);
  void run_op(std::unique_ptr<PositionOp> op);

  int tailAsync(std::function<void(int, uint64_t)> cb) override;
  int appendAsync(const std::string& data,
      std::function<void(int, uint64_t position)> cb) override;
  int readAsync(uint64_t position,
      std::function<void(int, std::string&)> cb) override;
  int fillAsync(uint64_t position, std::function<void(int)> cb) override;
  int trimAsync(uint64_t position, std::function<void(int)> cb) override;
  int trimTo(uint64_t position) override;
  int trimToAsync(uint64_t position, std::function<void(int)> cb) override;

 public:
  std::atomic<uint64_t> append_propose_sequencer;
  std::atomic<uint64_t> append_expand_view;
  std::atomic<uint64_t> append_seal;
  std::atomic<uint64_t> append_stale_view;
  std::atomic<uint64_t> append_read_only;

  void PrintStats() override;

 public:
  bool shutdown;
  std::mutex lock;

  // thread-safe
  const std::shared_ptr<LogBackend> backend;

  const std::string name;

  const std::unique_ptr<ViewManager> view_mgr;

  std::string exclusive_cookie;
  uint64_t exclusive_position;
  bool exclusive_empty;

  uint32_t num_inflight_ops_;
  std::list<std::pair<bool,
    std::condition_variable*>> queue_op_waiters_;

  const Options options;
};

class ReadOnlyLogImpl : public LogImpl {
 public:
  ReadOnlyLogImpl(const ReadOnlyLogImpl&) = delete;
  ReadOnlyLogImpl(const ReadOnlyLogImpl&&) = delete;
  ReadOnlyLogImpl& operator=(const ReadOnlyLogImpl&) = delete;
  ReadOnlyLogImpl& operator=(const ReadOnlyLogImpl&&) = delete;

  ReadOnlyLogImpl(std::shared_ptr<LogBackend> backend,
      const std::string& name,
      std::unique_ptr<ViewManager> view_mgr,
      const Options& opts) :
    LogImpl(backend, name, std::move(view_mgr), opts)
  {}

  ~ReadOnlyLogImpl() {}

  int Append(const std::string& data, uint64_t *pposition) override {
    return -EROFS;
  }

  int appendAsync(const std::string& data,
      std::function<void(int, uint64_t position)> cb) override {
    return -EROFS;
  }

  int Fill(uint64_t position) override {
    return -EROFS;
  }

  int fillAsync(uint64_t position, std::function<void(int)> cb) override {
    return -EROFS;
  }

  int Trim(uint64_t position) override {
    return -EROFS;
  }

  int trimAsync(uint64_t position, std::function<void(int)> cb) override {
    return -EROFS;
  }

  int trimTo(uint64_t position) override {
    return -EROFS;
  }

  int trimToAsync(uint64_t position, std::function<void(int)> cb) override {
    return -EROFS;
  }
};

int create_or_open(const Options& options,
    const std::string& name,
    std::shared_ptr<LogBackend>& log_backend_out,
    bool& created_out);

template<typename L>
int build_log_impl(const Options& options,
    const std::string& name, Log **logpp);
}
