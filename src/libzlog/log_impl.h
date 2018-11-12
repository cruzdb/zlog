#pragma once
#include <condition_variable>
#include <list>
#include <mutex>
#include <thread>

#include "include/zlog/log.h"
#include "include/zlog/statistics.h"
#include "libseq/libseqr.h"
#include "include/zlog/backend.h"
#include "striper.h"

#define DEFAULT_STRIPE_SIZE 100

namespace zlog {

typedef Backend *(*backend_allocate_t)(void);
typedef void (*backend_release_t)(Backend*);

class LogOp {
 public:
  LogOp(LogImpl *log) :
    log_(log)
  {}

  virtual ~LogOp() {}
  virtual int run() = 0;
  virtual void callback(int ret) = 0;

 protected:
  LogImpl *log_;
};

class TailOp : public LogOp {
 public:
  TailOp(LogImpl *log, bool increment, std::function<void(int, uint64_t)> cb) :
    LogOp(log),
    increment_(increment),
    cb_(cb)
  {}

  int run() override;

  void callback(int ret) override {
    if (cb_) {
      cb_(ret, position_);
    }
  }

 private:
  bool increment_;
  uint64_t position_;
  std::function<void(int, uint64_t)> cb_;
};

class TrimOp : public LogOp {
 public:
  TrimOp(LogImpl *log, uint64_t position, std::function<void(int)> cb) :
    LogOp(log),
    position_(position),
    cb_(cb)
  {}

  int run() override;

  void callback(int ret) override {
    if (cb_) {
      cb_(ret);
    }
  }

 private:
  uint64_t position_;
  std::function<void(int)> cb_;
};

class FillOp : public LogOp {
 public:
  FillOp(LogImpl *log, uint64_t position, std::function<void(int)> cb) :
    LogOp(log),
    position_(position),
    cb_(cb)
  {}

  int run() override;

  void callback(int ret) override {
    if (cb_) {
      cb_(ret);
    }
  }

 private:
  uint64_t position_;
  std::function<void(int)> cb_;
};

class ReadOp : public LogOp {
 public:
  ReadOp(LogImpl *log, uint64_t position,
      std::function<void(int, std::string&)> cb) :
    LogOp(log),
    position_(position),
    cb_(cb)
  {}

  int run() override;

  void callback(int ret) override {
    if (cb_) {
      cb_(ret, data_);
    }
  }

 private:
  uint64_t position_;
  std::string data_;
  std::function<void(int, std::string&)> cb_;
};

// TODO: move or copy or reference for the data
class AppendOp : public LogOp {
 public:
  AppendOp(LogImpl *log, const std::string& data,
      std::function<void(int, uint64_t)> cb) :
    LogOp(log),
    data_(data.data(), data.size()),
    position_epoch_(boost::none),
    cb_(cb)
  {}

  int run() override;

  void callback(int ret) override {
    if (cb_) {
      cb_(ret, position_);
    }
  }

 private:
  std::string data_;
  uint64_t position_;
  boost::optional<uint64_t> position_epoch_;
  std::function<void(int, uint64_t)> cb_;
};

class LogImpl : public Log {
 public:
  LogImpl(const LogImpl&) = delete;
  LogImpl(const LogImpl&&) = delete;
  LogImpl& operator=(const LogImpl&) = delete;
  LogImpl& operator=(const LogImpl&&) = delete;

  LogImpl(std::shared_ptr<Backend> backend,
      const std::string& name,
      const std::string& hoid,
      const std::string& prefix,
      const std::string& secret,
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
  std::list<std::unique_ptr<LogOp>> pending_ops_;
  void queue_op(std::unique_ptr<LogOp> op);

  int tailAsync(bool increment, std::function<void(int, uint64_t)> cb);
  int tailAsync(std::function<void(int, uint64_t)> cb) override {
    return tailAsync(false, cb);
  }
  int appendAsync(const std::string& data,
      std::function<void(int, uint64_t position)> cb) override;
  int readAsync(uint64_t position,
      std::function<void(int, std::string&)> cb) override;
  int fillAsync(uint64_t position, std::function<void(int)> cb) override;
  int trimAsync(uint64_t position, std::function<void(int)> cb) override;

 public:
  int StripeWidth() override {
    assert(0);
    // FIXME
    return -EINVAL;
  }

 public:
  bool shutdown;
  std::mutex lock;

  // thread-safe
  const std::shared_ptr<Backend> backend;

  const std::string name;
  const std::string hoid;
  const std::string prefix;

  Striper striper;

  std::string exclusive_cookie;
  uint64_t exclusive_position;
  bool exclusive_empty;

  const Options options;
};

}
