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

#include "proto/zlog.pb.h"
#include "include/zlog/log.h"
#include "include/zlog/backend.h"
#include "include/zlog/cache.h"

#include "fakeseqr.h"
#include "striper.h"

namespace zlog {

int LogImpl::Open(const std::string& scheme, const std::string& name,
    const std::map<std::string, std::string>& opts, LogImpl **logpp,
    std::shared_ptr<Backend> *out_backend)
{
  std::shared_ptr<Backend> backend;
  int ret = Backend::Load(scheme, opts, backend);
  if (ret)
    return ret;

  if (out_backend)
    *out_backend = backend;

  std::string hoid;
  std::string prefix;
  ret = backend->OpenLog(name, hoid, prefix);
  if (ret) {
    std::cerr << "failed to open log backend " << ret << std::endl;
    return ret;
  }

  Options options;

  auto log = std::unique_ptr<zlog::LogImpl>(
      new zlog::LogImpl(backend, name, hoid, prefix, options));

  log->striper.refresh();

  // TODO: assert that a view has been established, or is that handled on demand
  // in the case that something happened during initialization?
  // if (log->striper.Empty()) {
  //   return -EINVAL;
  // }

  *logpp = log.release();

  return 0;
}

LogImpl::~LogImpl()
{ 
  {
    std::lock_guard<std::mutex> l(lock);
    shutdown = true;
  }
  
  #ifdef WITH_STATS
  if(metrics_http_server_){
    metrics_http_server_->removeHandler("/metrics");
    metrics_http_server_->close();
    delete metrics_http_server_;
  }
  #endif

  striper.shutdown();
}

int LogImpl::CheckTail(uint64_t *pposition)
{
  return CheckTail(pposition, false);
}

int LogImpl::CheckTail(uint64_t *pposition, bool increment)
{
  while (true) {
    const auto view = striper.view();
    if (view->seq) {
      // TODO: obviously this is horable and awful.
      // TODO: we should rethink the checktail api too
      int ret = view->seq->CheckTail(view->epoch(), backend->meta(),
          name, pposition, increment);
      if (!ret) {
        return 0;
      } else if (ret == -EAGAIN) {
        sleep(1);
        continue;
      } else if (ret == -ERANGE) {
        striper.refresh(view->epoch());
        continue;
      }
      return ret;
    } else {
      int ret = striper.propose_sequencer(view, options);
      if (ret && ret != -ESPIPE) {
        return ret;
      }
      striper.refresh(view->epoch());
      continue;
    }
  }
}

int LogImpl::Read(const uint64_t position, std::string *data)
{
  while (true) {
    const auto view = striper.view();
    const auto oid = view->object_map.map(position);
    if (!oid) {
      int ret = striper.ensure_mapping(position);
      if (ret < 0) {
        return ret;
      }
      continue;
    }

    int ret = backend->Read(*oid, view->epoch(), position, 0, data);
    if (!ret) {
      return 0;
    }

    if (ret == -ESPIPE) {
      striper.refresh();
      continue;
    }

    // the mapping exists, but the object does. therefore, the entry doesn't
    // exist. just return enoent.
    //if (ret == -ENOENT) {
    //  backend->Seal(*oid, view->epoch());
    //  // TODO: we shouldn't ignore the return value here, but there isn't much
    //  // to do. if it succeeds, cool. if it shows that it's already been sealed
    //  // that's fine too since we reuse seal for object init and we want to init
    //  // here. maybe if there is a connection issue we should not spin... but we
    //  // can add that later.
    //  continue;
    //}

    return ret;
  }
}

int LogImpl::Append(const Slice& data, uint64_t *pposition)
{
  while (true) {
    const auto view = striper.view();

    uint64_t position;
    if (view->seq) {
      // TODO: unify with LogImpl::CheckTail
      // TODO: obviously this is horable and awful.
      int ret = view->seq->CheckTail(view->epoch(), backend->meta(),
          name, &position, true);
      if (ret) {
        if (ret == -EAGAIN) {
          sleep(1);
          continue;
        } else if (ret == -ERANGE) {
          striper.refresh(view->epoch());
          continue;
        }
        return ret;
      }
    } else {
      int ret = striper.propose_sequencer(view, options);
      if (ret && ret != -ESPIPE) {
        return ret;
      }
      striper.refresh(view->epoch());
      continue;
    }

    const auto oid = view->object_map.map(position);
    if (!oid) {
      int ret = striper.ensure_mapping(position);
      if (ret < 0) {
        return ret;
      }
      continue;
    }

    int ret = backend->Write(*oid, data, view->epoch(), position, 0);
    if (!ret) {
      if (pposition){
        *pposition = position;
      }
      return 0;
    }

    // TODO: return values on backend changed with ceph-ng
    if (ret == -ESPIPE) {
      striper.refresh();
      continue;
    }

    if (ret == -ENOENT) {
      backend->Seal(*oid, view->epoch());
      // TODO: we shouldn't ignore the return value here, but there isn't much
      // to do. if it succeeds, cool. if it shows that it's already been sealed
      // that's fine too since we reuse seal for object init and we want to init
      // here. maybe if there is a connection issue we should not spin... but we
      // can add that later.
      continue;
    }

    if (ret == -EROFS)
      continue;

    return ret;
  }
}

int LogImpl::Fill(const uint64_t position)
{
  while (true) {
    const auto view = striper.view();
    const auto oid = view->object_map.map(position);
    if (!oid) {
      int ret = striper.ensure_mapping(position);
      if (ret < 0) {
        return ret;
      }
      continue;
    }

    int ret = backend->Fill(*oid, view->epoch(), position, 0);
    if (!ret)
      return 0;
    if (ret == -ESPIPE) {
      striper.refresh();
      continue;
    } else if (ret == -ENOENT) {
      backend->Seal(*oid, view->epoch());
      // TODO: we shouldn't ignore the return value here, but there isn't much
      // to do. if it succeeds, cool. if it shows that it's already been sealed
      // that's fine too since we reuse seal for object init and we want to init
      // here. maybe if there is a connection issue we should not spin... but we
      // can add that later.
      continue;
    }
    return ret;
  }
}

int LogImpl::Trim(const uint64_t position)
{
  while (true) {
    const auto view = striper.view();
    const auto oid = view->object_map.map(position);
    if (!oid) {
      int ret = striper.ensure_mapping(position);
      if (ret < 0) {
        return ret;
      }
      continue;
    }

    // TODO: trim should be renamed to invalidate?
    int ret = backend->Trim(*oid, view->epoch(), position, 0);
    if (!ret){
      return 0;
    }
    // TODO: get some sort of unified / less fragile way of commnicating these
    // return vlaues.
    if (ret == -ESPIPE) {
      striper.refresh();
      continue;
    } else if (ret == -ENOENT) {
      backend->Seal(*oid, view->epoch());
      // TODO: we shouldn't ignore the return value here, but there isn't much
      // to do. if it succeeds, cool. if it shows that it's already been sealed
      // that's fine too since we reuse seal for object init and we want to init
      // here. maybe if there is a connection issue we should not spin... but we
      // can add that later.
      continue;
    }
    return ret;
  }
}

}
