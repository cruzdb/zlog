#include <boost/asio/ip/host_name.hpp>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <iostream>
#include <dlfcn.h>
#include "zlog/log.h"
#include "zlog/cache.h"
#include "zlog/backend.h"
#include "log_impl.h"

namespace zlog {

Log::~Log() {}

int Log::Open(const Options& options,
    const std::string& name, Log **logpp)
{
  if (name.empty()) {
    return -EINVAL;
  }

  std::shared_ptr<Backend> backend = options.backend;

  if (!backend) {
    int ret = Backend::Load(options.backend_name,
        options.backend_options, backend);
    if (ret) {
      return ret;
    }
  }

  bool created = false;
  std::unique_ptr<LogImpl> impl;
  while (!impl) {
    // try to open the log
    std::string hoid;
    std::string prefix;
    int ret = backend->OpenLog(name, hoid, prefix);
    if (ret && ret != -ENOENT) {
      return ret;
    }

    // if the log exists, build an instance
    if (ret == 0) {
      if (options.error_if_exists) {
        return -EEXIST;
      }

      impl = std::unique_ptr<LogImpl>(
          new LogImpl(backend, name, hoid, prefix, options));

    // otherwise, try to create the log
    } else {
      if (!options.create_if_missing) {
        return -ENOENT;
      }

      const auto init_view = View::create_initial();

      ret = backend->CreateLog(name, init_view, hoid, prefix);
      if (ret) {
        if (ret == -EEXIST) {
          if (options.error_if_exists) {
            return -EEXIST;
          }
          // retry the open
          continue;
        } else {
          return ret;
        }
      } else {
        created = true;
        impl = std::unique_ptr<LogImpl>(
            new LogImpl(backend, name, hoid, prefix, options));
      }
    }
  }

  if (options.prefault_position) {
    // call something like ensure mapping
  }

  (void)created;

  *logpp = impl.release();

  return 0;
}

}
