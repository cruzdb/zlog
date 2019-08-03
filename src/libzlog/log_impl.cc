#include "log_impl.h"
#include "op.h"

#include <cerrno>
#include <condition_variable>
#include <iostream>
#include <mutex>
#include <sstream>
#include <string>
#include <vector>
#include <boost/asio/ip/host_name.hpp>
#include <dlfcn.h>
#include <stdlib.h>

#include "include/zlog/log.h"
#include "include/zlog/backend.h"
#include "include/zlog/cache.h"

namespace zlog {

LogImpl::LogImpl(std::shared_ptr<LogBackend> backend,
    const std::string& name,
    std::unique_ptr<ViewManager> view_mgr,
    const Options& opts) :
  shutdown(false),
  backend(backend),
  name(name),
  view_mgr(std::move(view_mgr)),
  num_inflight_ops_(0),
  options(opts)
{
  assert(!this->name.empty());
  assert(this->view_mgr);

  for (int i = 0; i < options.finisher_threads; i++) {
    finishers_.push_back(std::thread(&LogImpl::finisher_entry_, this));
  }
}

LogImpl::~LogImpl()
{ 
  {
    std::lock_guard<std::mutex> l(lock);
    shutdown = true;
  }
  
  finishers_cond_.notify_all();
  for (auto& finisher : finishers_) {
    finisher.join();
  }

  view_mgr->shutdown();
}

void LogImpl::try_op(PositionOp& op)
{
  auto view = view_mgr->view();
  op.set_view(view);
  if (op.prepare()) {
    op.run();
  }
}

void LogImpl::run_op(std::unique_ptr<PositionOp> op)
{
  while (!op->done()) {
    try_op(*op);
  }
}

int LogImpl::tailAsync(std::function<void(int, uint64_t)> cb)
{
  auto op = std::unique_ptr<PositionOp>(new TailOp(this, cb));
  queue_op(std::move(op));
  return 0;
}

int LogImpl::tail(uint64_t *position_out)
{
  struct {
    int ret;
    bool done = false;
    uint64_t position;
    std::mutex lock;
    std::condition_variable cond;
  } ctx;

  int ret = tailAsync([&](int ret, uint64_t position) {
    {
      std::lock_guard<std::mutex> lk(ctx.lock);
      ctx.ret = ret;
      ctx.done = true;
      if (!ctx.ret) {
        ctx.position = position;
      }
      // XXX: document the race here with the caller
      ctx.cond.notify_one();
    }
  });

  if (ret) {
    return ret;
  }

  std::unique_lock<std::mutex> lk(ctx.lock);
  ctx.cond.wait(lk, [&] { return ctx.done; });

  if (!ctx.ret) {
    *position_out = ctx.position;
  }

  return ctx.ret;
}

int LogImpl::readAsync(uint64_t position,
    std::function<void(int, std::string&)> cb)
{
  auto op = std::unique_ptr<PositionOp>(new ReadOp(this, position, cb));
  queue_op(std::move(op));
  return 0;
}

int LogImpl::read(const uint64_t position, std::string *data_out)
{
  struct {
    int ret;
    bool done = false;
    std::string data;
    std::mutex lock;
    std::condition_variable cond;
  } ctx;

  int ret = readAsync(position, [&](int ret, std::string& data) {
    {
      std::lock_guard<std::mutex> lk(ctx.lock);
      ctx.ret = ret;
      ctx.done = true;
      if (!ctx.ret) {
        ctx.data.assign(std::move(data));
      }
      ctx.cond.notify_one();
    }
  });

  if (ret) {
    return ret;
  }

  std::unique_lock<std::mutex> lk(ctx.lock);
  ctx.cond.wait(lk, [&] { return ctx.done; });

  if (!ctx.ret) {
    data_out->assign(std::move(ctx.data));
  }

  return ctx.ret;
}

int LogImpl::appendAsync(const std::string& data,
    std::function<void(int, uint64_t)> cb)
{
  auto op = std::unique_ptr<PositionOp>(new AppendOp(this, data, cb));
  queue_op(std::move(op));
  return 0;
}

int LogImpl::append(const std::string& data, uint64_t *pposition)
{
  struct {
    int ret;
    bool done = false;
    uint64_t position;
    std::mutex lock;
    std::condition_variable cond;
  } ctx;

  int ret = appendAsync(data, [&](int ret, uint64_t position) {
    {
      std::lock_guard<std::mutex> lk(ctx.lock);
      ctx.ret = ret;
      ctx.done = true;
      if (!ctx.ret) {
        ctx.position = position;
      }
      ctx.cond.notify_one();
    }
  });

  if (ret) {
    return ret;
  }

  std::unique_lock<std::mutex> lk(ctx.lock);
  ctx.cond.wait(lk, [&] { return ctx.done; });

  if (!ctx.ret && pposition) {
    *pposition = ctx.position;
  }

  return ctx.ret;
}

int LogImpl::fillAsync(uint64_t position, std::function<void(int)> cb)
{
  auto op = std::unique_ptr<PositionOp>(new FillOp(this, position, cb));
  queue_op(std::move(op));
  return 0;
}

int LogImpl::fill(const uint64_t position)
{
  struct {
    int ret;
    bool done = false;
    std::mutex lock;
    std::condition_variable cond;
  } ctx;

  int ret = fillAsync(position, [&](int ret) {
    {
      std::lock_guard<std::mutex> lk(ctx.lock);
      ctx.ret = ret;
      ctx.done = true;
      ctx.cond.notify_one();
    }
  });

  if (ret) {
    return ret;
  }

  std::unique_lock<std::mutex> lk(ctx.lock);
  ctx.cond.wait(lk, [&] { return ctx.done; });

  return ctx.ret;
}

int LogImpl::trimAsync(uint64_t position, std::function<void(int)> cb)
{
  auto op = std::unique_ptr<PositionOp>(new TrimOp(this, position, cb));
  queue_op(std::move(op));
  return 0;
}

int LogImpl::trim(const uint64_t position)
{
  struct {
    int ret;
    bool done = false;
    std::mutex lock;
    std::condition_variable cond;
  } ctx;

  int ret = trimAsync(position, [&](int ret) {
    {
      std::lock_guard<std::mutex> lk(ctx.lock);
      ctx.ret = ret;
      ctx.done = true;
      ctx.cond.notify_one();
    }
  });

  if (ret) {
    return ret;
  }

  std::unique_lock<std::mutex> lk(ctx.lock);
  ctx.cond.wait(lk, [&] { return ctx.done; });

  return ctx.ret;
}

int LogImpl::trimTo(const uint64_t position)
{
  struct {
    int ret;
    bool done = false;
    std::mutex lock;
    std::condition_variable cond;
  } ctx;

  int ret = trimToAsync(position, [&](int ret) {
    {
      std::lock_guard<std::mutex> lk(ctx.lock);
      ctx.ret = ret;
      ctx.done = true;
      ctx.cond.notify_one();
    }
  });

  if (ret) {
    return ret;
  }

  std::unique_lock<std::mutex> lk(ctx.lock);
  ctx.cond.wait(lk, [&] { return ctx.done; });

  return ctx.ret;
}

int LogImpl::trimToAsync(uint64_t position, std::function<void(int)> cb)
{
  auto op = std::unique_ptr<PositionOp>(new TrimToOp(this, position, cb));
  queue_op(std::move(op));
  return 0;
}

void LogImpl::queue_op(std::unique_ptr<PositionOp> op)
{
  std::unique_lock<std::mutex> lk(lock);

  if (num_inflight_ops_ >= options.max_inflight_ops) {
    std::condition_variable cond;
    queue_op_waiters_.emplace_front(false, &cond);
    auto it = queue_op_waiters_.begin();
    cond.wait(lk, [&] {
      assert(it->second == &cond);
      return it->first;
    });
    queue_op_waiters_.erase(it);
  }

  num_inflight_ops_++;

  pending_ops_.emplace_back(std::move(op));
  finishers_cond_.notify_all();
}

void LogImpl::finisher_entry_()
{
  while (true) {
    bool do_shutdown = false;
    std::unique_ptr<PositionOp> op;
    {
      std::unique_lock<std::mutex> lk(lock);
      finishers_cond_.wait(lk, [&] {
        return !pending_ops_.empty() || shutdown;
      });

      if (shutdown) {
        if (pending_ops_.empty()) {
          break;
        }
        do_shutdown = true;
      }

      assert(!pending_ops_.empty());
      op = std::move(pending_ops_.front());
      pending_ops_.pop_front();
    }

    if (do_shutdown) {
      op->callback(-ESHUTDOWN);
    } else {
      run_op(std::move(op));
    }

    std::lock_guard<std::mutex> lk(lock);
    assert(num_inflight_ops_ > 0);
    num_inflight_ops_--;
    if (!queue_op_waiters_.empty()) {
      queue_op_waiters_.back().first = true;
      queue_op_waiters_.back().second->notify_one();
    }
  }
}

}
