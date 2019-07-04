#include "log_impl.h"

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

#include "striper.h"

namespace zlog {

LogImpl::LogImpl(std::shared_ptr<Backend> backend,
    const std::string& name,
    const std::string& hoid,
    const std::string& prefix,
    const std::string& secret,
    const Options& opts) :
  shutdown(false),
  backend(backend),
  name(name),
  hoid(hoid),
  prefix(prefix),
  striper(this, secret),
  num_inflight_ops_(0),
  options(opts)
{
  assert(!name.empty());
  assert(!hoid.empty());
  assert(!prefix.empty());

  for (int i = 0; i < options.finisher_threads; i++) {
    finishers_.push_back(std::thread(&LogImpl::finisher_entry_, this));
  }

  append_propose_sequencer = 0;
  append_expand_view = 0;
  append_seal = 0;
  append_stale_view = 0;
  append_read_only = 0;
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

  striper.shutdown();
}

int TailOp::run()
{
  while (true) {
    const auto view = log_->striper.view();
    if (view->seq) {
      position_ = view->seq->check_tail(increment_);
      return 0;
    } else {
      int ret = log_->striper.propose_sequencer();
      if (ret) {
        return ret;
      }
      continue;
    }
  }
}

int LogImpl::tailAsync(bool increment, std::function<void(int, uint64_t)> cb)
{
  auto op = std::unique_ptr<LogOp>(new TailOp(this, increment, cb));
  queue_op(std::move(op));
  return 0;
}

int LogImpl::CheckTail(uint64_t *position_out)
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

int ReadOp::run()
{
  while (true) {
    const auto view = log_->striper.view();
    const auto oid = log_->striper.map(view, position_);
    if (!oid) {
      int ret = log_->striper.try_expand_view(position_);
      if (ret) {
        return ret;
      }
      continue;
    }

    int ret = log_->backend->Read(*oid, view->epoch(), position_, &data_);

    if (ret == -ESPIPE) {
      log_->striper.update_current_view(view->epoch());
      continue;
    }

    if (ret == -ERANGE) {
      return -ENOENT;
    }

    // the position is mapped, but the target object doesn't exist / hasn't been
    // initialized. in this case we _could_ choose to not initialize it and
    // report that the position hasn't been written. initializing here means we
    // can avoid explaining how the behavior is correct, and unifies handling
    // with the other operations which will make future restructing of the async
    // handling easier. in the end, this is unlikely to be an optimization that
    // matters at all since newly created stripes are initialized in the
    // background (future work).
    if (ret == -ENOENT) {
      int ret = log_->backend->Seal(*oid, view->epoch());
      if (ret && ret != -ESPIPE) {
        return ret;
      }
      continue;
    }

    return ret;
  }
}

int LogImpl::Read(const uint64_t position, std::string *data_out)
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

int LogImpl::readAsync(uint64_t position,
    std::function<void(int, std::string&)> cb)
{
  auto op = std::unique_ptr<LogOp>(new ReadOp(this, position, cb));
  queue_op(std::move(op));
  return 0;
}

int AppendOp::run()
{
  while (true) {
    const auto view = log_->striper.view();

    if (view->seq) {
      // avoid obtaining a new append position when the view has been updated
      // (e.g. because the mapping was extended), but the sequencer did not
      // change. this is generally a minor optimization. but for completeness,
      // it also handles the edge case in which stripes are configured to hold
      // exactly one log entry. in this case a loop will be created by which the
      // new position doesn't map, the map is extended, and then a new unmapped
      // position is obtained.
      if (!position_epoch_ || (*position_epoch_ != view->seq->epoch())) {
        position_ = view->seq->check_tail(true);
        position_epoch_ = view->seq->epoch();
      }
      assert(position_epoch_);
      assert(*position_epoch_ > 0);
      assert(*position_epoch_ == view->seq->epoch());
    } else {
      log_->append_propose_sequencer++;
      int ret = log_->striper.propose_sequencer();
      if (ret) {
        return ret;
      }
      continue;
    }

    const auto oid = log_->striper.map(view, position_);
    if (!oid) {
      log_->append_expand_view++;
      int ret = log_->striper.try_expand_view(position_);
      if (ret) {
        return ret;
      }
      continue;
    }

    while (true) {
      int ret = log_->backend->Write(*oid, data_, view->epoch(), position_);
      if (!ret) {
        return ret;
      } else if (ret == -ENOENT) {
        log_->append_seal++;
        // this can happen if a new stripe has been created but not initialized,
        // either because we are racing with initialization, or due to a fault in
        // the process performing the initialization.
        int ret = log_->backend->Seal(*oid, view->epoch());
        if (!ret) {
          // try the append again. the view and the position are still
          // consistent, and there is no reason to think they are out-of-date.
          continue;
        } else if (ret != -ESPIPE) {
          return ret;
        }
        assert(ret == -ESPIPE);
        // unlike other backend interfaces, seal will return -ESPIPE if the
        // epoch is less than _or equal_ to the stored epoch. if the write
        // returned -ENOENT at epoch 100 because it was racing with
        // initialization (also at epoch 100), then seal at epoch 100 will
        // return -ESPIPE. the point is that when -ESPIPE is returned from seal
        // we shouldn't refresh the striper and wait on a newer epoch. if there
        // actually is a newer view, then that will be caught by the write
        // interface. XXX: this would be a fantastic scenario to test for in a
        // model, by incorrectly refreshing here causing a deadlock, or perhaps
        // changing the epoch <= test in the backend.
        break;
      } else if (ret == -ESPIPE) {
        log_->append_stale_view++;
        log_->striper.update_current_view(view->epoch());
        break;
      } else if (ret == -EROFS) {
        log_->append_read_only++;
        position_epoch_.reset(); // make sure to get a new position
        break;
      } else {
        return ret;
      }
    }
  }
}

int LogImpl::Append(const std::string& data, uint64_t *pposition)
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

int LogImpl::appendAsync(const std::string& data,
    std::function<void(int, uint64_t)> cb)
{
  auto op = std::unique_ptr<LogOp>(new AppendOp(this, data, cb));
  queue_op(std::move(op));
  return 0;
}

int FillOp::run()
{
  while (true) {
    const auto view = log_->striper.view();
    const auto oid = log_->striper.map(view, position_);
    if (!oid) {
      int ret = log_->striper.try_expand_view(position_);
      if (ret) {
        return ret;
      }
      continue;
    }

    int ret = log_->backend->Fill(*oid, view->epoch(), position_);

    if (ret == -ESPIPE) {
      log_->striper.update_current_view(view->epoch());
      continue;
    }

    if (ret == -ENOENT) {
      int ret = log_->backend->Seal(*oid, view->epoch());
      if (ret && ret != -ESPIPE) {
        return ret;
      }
      continue;
    }

    return ret;
  }
}

int LogImpl::Fill(const uint64_t position)
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

int LogImpl::fillAsync(uint64_t position, std::function<void(int)> cb)
{
  auto op = std::unique_ptr<LogOp>(new FillOp(this, position, cb));
  queue_op(std::move(op));
  return 0;
}

int TrimOp::run()
{
  while (true) {
    const auto view = log_->striper.view();
    const auto oid = log_->striper.map(view, position_);
    if (!oid) {
      int ret = log_->striper.try_expand_view(position_);
      if (ret) {
        return ret;
      }
      continue;
    }

    int ret = log_->backend->Trim(*oid, view->epoch(), position_,
        false, false);

    if (ret == -ESPIPE) {
      log_->striper.update_current_view(view->epoch());
      continue;
    }

    if (ret == -ENOENT) {
      int ret = log_->backend->Seal(*oid, view->epoch());
      if (ret && ret != -ESPIPE) {
        return ret;
      }
      continue;
    }

    return ret;
  }
}

int LogImpl::Trim(const uint64_t position)
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

int LogImpl::trimAsync(uint64_t position, std::function<void(int)> cb)
{
  auto op = std::unique_ptr<LogOp>(new TrimOp(this, position, cb));
  queue_op(std::move(op));
  return 0;
}

int TrimToOp::run()
{
  while (true) {
    const auto view = log_->striper.view();
    // note that we are invalidating the range [0, position_], inclusive. this
    // results in a _valid_ range of [_position+1, ...) which is why we _advance
    // the valid position_ to position_ + 1.
    if (position_ >= view->object_map().min_valid_position()) {
      int ret = log_->striper.advance_min_valid_position(position_ + 1);
      if (ret) {
        return ret;
      }
      continue;
    }

    uint64_t stripe_id = 0;
    bool done = false;
    bool restart = false;

    // drives the iterator over the map_to range
    while (true) {
      // get all objects that map positions in the trim range
      // TODO: would be good to skip objects already processed
      const auto objects = log_->striper.map_to(view, position_, stripe_id, done);
      if (done) {
        break;
      }

      if (!objects) {
        // expand view may also attempt to initialize new stripes. this is
        // correct, but inefficient. however, trimming/space reclaiming right now
        // has a lot of ineffiencies and this can be address in a later revision
        // that will address the problem of trimming/space reclaiming/object
        // deletion/view trimming more completely.
        int ret = log_->striper.try_expand_view(position_);
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
        int ret = log_->backend->Trim(oid, view->epoch(), position_,
            true, trim_full);

        if (ret == -ESPIPE) {
          log_->striper.update_current_view(view->epoch());
          // restart after view update. wildly inefficient :(
          restart = true;
          break;
        }

        if (ret == -ENOENT) {
          int ret = log_->backend->Seal(oid, view->epoch());
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
  auto op = std::unique_ptr<LogOp>(new TrimToOp(this, position, cb));
  queue_op(std::move(op));
  return 0;
}

void LogImpl::queue_op(std::unique_ptr<LogOp> op)
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
    std::unique_ptr<LogOp> op;
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
      int ret = op->run();
      op->callback(ret);
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

void LogImpl::PrintStats()
{
  std::cout << "==== stats ===========================" << std::endl;
  std::cout << "append_propose_sequencer = " << append_propose_sequencer << std::endl;
  std::cout << "append_expand_view = " << append_expand_view << std::endl;
  std::cout << "append_seal = " << append_seal << std::endl;
  std::cout << "append_stale_view = " << append_stale_view << std::endl;
  std::cout << "append_read_only = " << append_read_only << std::endl;
  std::cout << "======================================" << std::endl;
}

}
