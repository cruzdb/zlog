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

int create_or_open(const Options& options,
    Backend *backend, const std::string& name,
    std::string *hoid_out, std::string *prefix_out)
{
  std::string hoid;
  std::string prefix;
  boost::optional<std::string> view;

  while (true) {
    int ret = backend->OpenLog(name, &hoid, &prefix);
    if (ret && ret != -ENOENT) {
      return ret;
    }

    if (ret == 0) {
      if (options.error_if_exists) {
        return -EEXIST;
      }

      break;
    }

    if (!options.create_if_missing) {
      return -ENOENT;
    }

    if (!view) {
      view = View::create_initial();
    }

    ret = backend->CreateLog(name, *view, &hoid, &prefix);
    if (ret) {
      if (ret == -EEXIST) {
        if (options.error_if_exists) {
          return -EEXIST;
        }
        continue;
      } else {
        return ret;
      }
    }

    break;
  }

  hoid_out->swap(hoid);
  prefix_out->swap(prefix);

  return 0;
}

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

  std::string hoid;
  std::string prefix;
  int ret = create_or_open(options, backend.get(),
      name, &hoid, &prefix);
  if (ret) {
    return ret;
  }

  uint64_t unique_id;
  ret = backend->uniqueId(hoid, &unique_id);
  if (ret) {
    return ret;
  }

  std::stringstream secret;
  secret << "zlog.secret."
         << name << "." << hoid << "."
         << boost::asio::ip::host_name() << "."
         << unique_id;

  auto impl = std::unique_ptr<LogImpl>(
      new LogImpl(backend, name, hoid, prefix, secret.str(), options));

  *logpp = impl.release();

  return 0;
}

}
