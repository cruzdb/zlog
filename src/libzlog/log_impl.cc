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

// TODO: would be good to skip objects already processed
int LogImpl::gc()
{
  while (true) {
    const auto view = view_mgr->view();

    if (view->object_map().min_valid_position() == 0) {
      return 0;
    }

    const auto max_invalid_position =
      view->object_map().min_valid_position() - 1;

    uint64_t stripe_id = 0;
    bool done = false;
    bool restart = false;

    while (true) {
      const auto objects = view_mgr->map_to(view, max_invalid_position,
          stripe_id, done);
      if (done) {
        break;
      }

      if (!objects) {
        // expand view may also attempt to initialize new stripes. this is
        // correct, but inefficient. however, trimming/space reclaiming right now
        // has a lot of ineffiencies and this can be address in a later revision
        // that will address the problem of trimming/space reclaiming/object
        // deletion/view trimming more completely.
        int ret = view_mgr->try_expand_view(max_invalid_position);
        if (ret) {
          return ret;
        }
        restart = true;
        break;
      }

      for (auto obj : *objects) {
        const auto oid = obj.first;
        const auto trim_full = obj.second;

        // handles setting up range trim and omap/bytestream space reclaim etc..
        int ret = backend->Trim(oid, view->epoch(), max_invalid_position,
            true, trim_full);

        if (ret == -ESPIPE) {
          view_mgr->update_current_view(view->epoch());
          restart = true;
          break;
        }

        if (ret == -ENOENT) {
          int ret = backend->Seal(oid, view->epoch());
          if (ret && ret != -ESPIPE) {
            return ret;
          }

          // part of trimming here means we may create objects that are
          // immediately trimmed (holes, past eol). i suspect that there are an
          // optimization here, but for now when we create a new object we'll
          // restart the trim process and treat it like any other object. this is
          // clearly, wildly, inefficient.
          restart = true;
          break;
        }

        if (ret != 0) {
          return ret;
        }
      }

      if (restart)
        break;
    }

    if (restart)
      continue;

    break;
  }

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
