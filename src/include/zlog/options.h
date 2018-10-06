#pragma once
#include <memory>
#include <string>
#include <vector>
#include <map>
#include <boost/optional.hpp>
#include "eviction.h"
#include "statistics.h"

namespace zlog {

class Statistics;
class Backend;

struct Options {
  // The storage backend. When set, this option will take priority over other
  // options used when constructing the storage backend instance.
  std::shared_ptr<Backend> backend = nullptr;

  // Name of the storage backend to instatiate (e.g. ram, lmdb, ceph).
  std::string backend_name;

  // Backend-specific configuration options.
  std::map<std::string, std::string> backend_options;

  bool create_if_missing = false;
  bool error_if_exists = false;

  boost::optional<uint64_t> prefault_position = 0;

  ///////////////////////////////////////////////////////////////////


  int width = 10;
  int entries_per_object = 200;

  Statistics* statistics = nullptr;
  std::vector<std::string> http;
  
  //cache options
  zlog::Eviction::Eviction_Policy eviction = zlog::Eviction::Eviction_Policy::LRU;
  size_t cache_size = 1024 * 1024 * 1;
};

}
