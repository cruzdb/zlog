#include <boost/asio/ip/host_name.hpp>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <iostream>
#include <dlfcn.h>
#include "zlog/log.h"
#include "zlog/backend.h"
#include "log_impl.h"

namespace zlog {

Log::~Log() {}

int Log::Create(const Options& options,
    const std::string& scheme, const std::string& name,
    const std::map<std::string, std::string>& opts,
    const std::string& host, const std::string& port,
    Log **logpp)
{
  if (options.width <= 0) {
    std::cerr << "width must be great than 0" << std::endl;
    return -EINVAL;
  }

  if (options.entries_per_object <= 0) {
    std::cerr << "entries_per_object must be great than 0" << std::endl;
    return -EINVAL;
  }

  if (options.max_entry_size <= 0) {
    std::cerr << "max_entry_size must be great than 0" << std::endl;
    return -EINVAL;
  }

  std::shared_ptr<Backend> backend;
  int ret = Backend::Load(scheme, opts, backend);
  if (ret)
    return ret;

  // build the initial view
  std::string init_view_data;
  auto init_view = Striper::InitViewData(options.width, options.entries_per_object,
      options.max_entry_size);
  if (host.empty()) {
    auto uuid = boost::uuids::random_generator()();
    auto hostname = boost::asio::ip::host_name();
    std::stringstream exclusive_cookie_ss;
    exclusive_cookie_ss << uuid << "." << hostname
      << "." << 0;
    const auto cookie = exclusive_cookie_ss.str();

    init_view.set_exclusive_cookie(cookie);
  } else {
    init_view.set_host(host);
    init_view.set_port(port);
  }
  if (!init_view.SerializeToString(&init_view_data)) {
    std::cerr << "failed to serialize view" << std::endl;
    return -EIO;
  }

  ret = backend->CreateLog(name, init_view_data);
  if (ret) {
    std::cerr << "Failed to create log " << name << " ret "
      << ret << " (" << strerror(-ret) << ")" << std::endl;
    return ret;
  }

  std::string hoid;
  std::string prefix;
  ret = backend->OpenLog(name, hoid, prefix);
  if (ret) {
    return ret;
  }

  auto impl = std::unique_ptr<LogImpl>(
      new LogImpl(backend, name, hoid, prefix, options));

  // make sure to set before update view
  if (init_view.has_exclusive_cookie()) {
    impl->exclusive_cookie = init_view.exclusive_cookie();
    impl->exclusive_empty = true;
    impl->exclusive_position = 0;
  }

  ret = impl->UpdateView();
  if (ret) {
    return ret;
  }

  if (impl->striper.Empty()) {
    return -EINVAL;
  }

  *logpp = impl.release();

  return 0;
}

int Log::Open(const Options& options,
    const std::string& scheme, const std::string& name,
    const std::map<std::string, std::string>& opts,
    const std::string& host, const std::string& port,
    Log **logpp)
{
  if (name.empty())
    return -EINVAL;

  std::shared_ptr<Backend> backend;
  int ret = Backend::Load(scheme, opts, backend);
  if (ret)
    return ret;

  std::string hoid;
  std::string prefix;
  ret = backend->OpenLog(name, hoid, prefix);
  if (ret) {
    return ret;
  }

  auto impl = std::unique_ptr<LogImpl>(
      new LogImpl(backend, name, hoid, prefix, options));

  ret = impl->UpdateView();
  if (ret) {
    return ret;
  }

  if (impl->striper.Empty()) {
    return -EINVAL;
  }

  // FIXME: these semantics are WEIRD. Also, we don't actually do anything with
  // host and port /)
  if (host.empty()) {
    ret = impl->ProposeExclusiveMode();
    if (ret) {
      return ret;
    }
  } else {
    ret = impl->ProposeSharedMode();
    if (ret) {
      return ret;
    }
  }

  *logpp = impl.release();

  return 0;
}

int Log::CreateWithBackend(const Options& options,
    std::shared_ptr<Backend> backend,
    const std::string& name, Log **logptr)
{
  if (options.width <= 0) {
    std::cerr << "width must be great than 0" << std::endl;
    return -EINVAL;
  }

  if (options.entries_per_object <= 0) {
    std::cerr << "entries_per_object must be great than 0" << std::endl;
    return -EINVAL;
  }

  if (options.max_entry_size <= 0) {
    std::cerr << "max_entry_size must be great than 0" << std::endl;
    return -EINVAL;
  }

  // build the initial view
  std::string init_view_data;
  auto init_view = Striper::InitViewData(options.width, options.entries_per_object,
      options.max_entry_size);
  auto uuid = boost::uuids::random_generator()();
  auto hostname = boost::asio::ip::host_name();
  std::stringstream exclusive_cookie_ss;
  exclusive_cookie_ss << uuid << "." << hostname
    << "." << 0;
  const auto cookie = exclusive_cookie_ss.str();

  init_view.set_exclusive_cookie(cookie);

  if (!init_view.SerializeToString(&init_view_data)) {
    std::cerr << "failed to serialize view" << std::endl;
    return -EIO;
  }

  int ret = backend->CreateLog(name, init_view_data);
  if (ret) {
    std::cerr << "Failed to create log " << name << " ret "
      << ret << " (" << strerror(-ret) << ")" << std::endl;
    return ret;
  }

  std::string hoid;
  std::string prefix;
  ret = backend->OpenLog(name, hoid, prefix);
  if (ret) {
    return ret;
  }

  auto impl = std::unique_ptr<LogImpl>(
      new LogImpl(backend, name, hoid, prefix, options));

  // make sure to set before update view
  impl->exclusive_cookie = init_view.exclusive_cookie();
  impl->exclusive_empty = true;
  impl->exclusive_position = 0;

  ret = impl->UpdateView();
  if (ret) {
    return ret;
  }

  if (impl->striper.Empty()) {
    return -EINVAL;
  }

  *logptr = impl.release();

  return 0;
}

int Log::OpenWithBackend(const Options& options,
    std::shared_ptr<Backend> backend,
    const std::string& name, Log **logptr)
{
  if (name.empty())
    return -EINVAL;

  std::string hoid;
  std::string prefix;
  int ret = backend->OpenLog(name, hoid, prefix);
  if (ret) {
    return ret;
  }

  auto impl = std::unique_ptr<LogImpl>(
      new LogImpl(backend, name, hoid, prefix, options));

  ret = impl->UpdateView();
  if (ret) {
    return ret;
  }

  if (impl->striper.Empty()) {
    return -EINVAL;
  }

  ret = impl->ProposeExclusiveMode();
  if (ret)
    return ret;

  *logptr = impl.release();

  return 0;
}

}
