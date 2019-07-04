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

  // add stripes to the initial view for new logs.
  bool create_initial_view_stripes = true;

  // schedule a background task to initialize stripe objects whenever a new
  // stripe is created. this should always be set to true, and is only false for
  // in testing scenarios (e.g. synchronous object init in i/o path).
  bool init_stripe_on_create = true;

  // TODO: per-backend defeaults and precedence (e.g. option, be, view)
  uint32_t stripe_width = 10;
  uint32_t stripe_slots = 5;

  uint32_t max_inflight_ops = 1024;

  ///////////////////////////////////////////////////////////////////

  // number of I/O threads
  int finisher_threads = 10;

  // maximum views to read at once when updating current view
  // advanced
  int max_refresh_views_read = 20;

  Statistics* statistics = nullptr;
  std::vector<std::string> http;
  
  //cache options
  zlog::Eviction::Eviction_Policy eviction = zlog::Eviction::Eviction_Policy::LRU;
  size_t cache_size = 1024 * 1024 * 1;
};

}
