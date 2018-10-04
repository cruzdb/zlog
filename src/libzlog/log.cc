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
  // TODO: validate options

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

      // TODO: make_unique
      impl = std::unique_ptr<LogImpl>(
          new LogImpl(backend, name, hoid, prefix, options));

    // otherwise, try to create the log
    } else {
      if (!options.create_if_missing) {
        return -ENOENT;
      }

      // TODO: create an option that controls how much state is stuffed into the
      // initial view, versus configured after creation, either in this method
      // or later by users of the log. this is an optimization that should be
      // added later after lots of testing without it. Currently the initial
      // view has no settings at all (no stripes, or sequencer info).
      const auto init_view = View::create_initial();

      // TODO: document that CreateLog is exclusive
      // TODO: return hoid if creation is successful
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
        // TODO: hoid here comes from CreateLog
        // TODO: actually... look at OpenLog. we may want to do OpenLog and then
        // verify that the log we opened has the same hoid.
        created = true;
        impl = std::unique_ptr<LogImpl>(
            new LogImpl(backend, name, hoid, prefix, options));
      }
    }
  }

  // ensure the log has storage mappings up to the prefault position. when a
  // prefault position is not defined and the log has no mappings (e.g. it was
  // just newly created) then the first mapping will be created in response to a
  // write operation. this is only useful for setting up test scenarios.
  if (options.prefault_position) {
    // call something like ensure mapping
  }

  (void)created;

#if 0
  // build the initial view
  std::string seq_cookie;
  std::string seq_host;
  std::string seq_port;

  if (host.empty()) {
    auto uuid = boost::uuids::random_generator()();
    auto hostname = boost::asio::ip::host_name();
    std::stringstream exclusive_cookie_ss;
    exclusive_cookie_ss << uuid << "." << hostname
      << "." << 0;
    seq_cookie = exclusive_cookie_ss.str();
  } else {
    seq_host = host;
    seq_port = port;
  }

  // TODO: striper::create_initial(...);
  //auto init_view = Striper::InitViewData(options.width, options.entries_per_object);
  auto init_view = View::create_initial(
      options.width, options.entries_per_object,
      seq_cookie, seq_host, seq_port);

  // make sure to set before update view. TODO: this is probably a bug since we
  // don't really know that the initial view is the one that is active. almost
  // certainly a bug.
  if (host.empty()) {
    impl->exclusive_cookie = seq_cookie;
    impl->exclusive_empty = true;
    impl->exclusive_position = 0;
  }
#endif

  // if we created the log then we can set the sequencer here based on options
  // that we have available. we can also NOT set the sequencer info, and it can
  // be created later in response to the client invoking log operations. like
  // prefault position being unspecified above, this is just for testing.

  // if the log already existed, then we want to give priority to whatever
  // sequencer is specified in the log, if any. if none is specified (no view or
  // its just empty), then fall back to options or defaults.

  *logpp = impl.release();

  return 0;
}

}
