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

// TODO
//  - it might be useful to create a wrapper to hold state like hoid, prefix,
//  etc.. and pass that around rather than each individual piece of state. since
//  we are building up the class hierachy from the bottom now, it's more
//  annoying to pass that state downward. but lets hold off, because it might
//  end up being the case that there isn't much sharing after the restructuring.
//
//  - become sequencer if relevant when the log instance is first created
//  instead of waiting for an appender. might even be worth while adding it to
//  the very first view.

namespace zlog {

Log::~Log() {}

int create_or_open(const Options& options, const std::string& name,
    std::shared_ptr<LogBackend>& log_backend_out, bool& created_out)
{
  if (name.empty()) {
    return -EINVAL;
  }

  // open the backend
  std::shared_ptr<Backend> backend = options.backend;
  if (!backend) {
    int ret = Backend::Load(options.backend_name,
        options.backend_options, backend);
    if (ret) {
      return ret;
    }
  }
  assert(backend);

  // create or open the log
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
      view = View::create_initial(options);
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
    created_out = true;
    break;
  }

  log_backend_out = std::make_shared<LogBackend>(backend, hoid, prefix);

  return 0;
}

int Log::Open(const Options& options,
    const std::string& name, Log **logpp)
{
  // create or open the log -> log backend
  bool created = false;
  std::shared_ptr<LogBackend> log_backend;
  int ret = create_or_open(options, name, log_backend, created);
  if (ret) {
    return ret;
  }
  assert(log_backend);

  uint64_t unique_id;
  ret = log_backend->uniqueId(&unique_id);
  if (ret) {
    return ret;
  }

  std::stringstream secret;
  secret << "zlog.secret."
         << name << "." << log_backend->hoid() << "."
         << boost::asio::ip::host_name() << "."
         << unique_id;

  auto view_reader = std::unique_ptr<ViewReader>(new ViewReader(
        log_backend, secret.str(), options));

  // initialize the reader with the latest view
  view_reader->refresh_view();
  if (!view_reader->view()) {
    return -EIO;
  }

  auto striper = std::unique_ptr<Striper>(new Striper(log_backend,
        std::move(view_reader), secret.str(), options));

  // kick start initialization of the objects in the first stripe
  if (options.init_stripe_on_create && created) {
    // is there actually is a stripe? this is controlled by the
    // create_init_view_stripes option
    if (!striper->view()->object_map().empty()) {
      striper->async_init_stripe(0);
    }
  }

  auto impl = std::unique_ptr<LogImpl>(new LogImpl(log_backend, name,
        std::move(striper), options));

  *logpp = impl.release();

  return 0;
}

}
