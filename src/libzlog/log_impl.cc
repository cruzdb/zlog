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

#include "striper.h"

namespace zlog {

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
      auto tail = view->seq->check_tail(increment);
      *pposition = tail;
      return 0;
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

    int ret = backend->Read(*oid, view->epoch(), position, data);
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
      position = view->seq->check_tail(true);
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

    int ret = backend->Write(*oid, data, view->epoch(), position);
    if (!ret) {
      if (pposition){
        *pposition = position;
      }
      return 0;
    }

    if (ret == -ESPIPE) {
      striper.refresh();
      continue;
    }

    if (ret == -ENOENT) {
      backend->Seal(*oid, view->epoch());
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

    int ret = backend->Fill(*oid, view->epoch(), position);
    if (!ret)
      return 0;
    if (ret == -ESPIPE) {
      striper.refresh();
      continue;
    } else if (ret == -ENOENT) {
      backend->Seal(*oid, view->epoch());
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

    int ret = backend->Trim(*oid, view->epoch(), position);
    if (!ret){
      return 0;
    }
    if (ret == -ESPIPE) {
      striper.refresh();
      continue;
    } else if (ret == -ENOENT) {
      backend->Seal(*oid, view->epoch());
      continue;
    }
    return ret;
  }
}

}
