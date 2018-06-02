#pragma once
#include <memory>
#include <string>
#include <vector>
#include "eviction.h"
#include "statistics.h"

namespace zlog {

class Statistics;

struct Options {
  // Number of objects to stripe the log across. This value is used to configure
  // a new log, and can be adjusted for a log after it has been created.
  // TODO: create an intelligent default
  // TODO: add reference to width adjustment api/tools
  // TODO: add option for create vs open (default and force new width)
  int width = 10;

  int entries_per_object = 200;

  int max_entry_size = 1024;

  std::shared_ptr<Statistics> statistics = nullptr;
  std::vector<std::string> http;
  
  //cache options
  zlog::Eviction::Eviction_Policy eviction = zlog::Eviction::Eviction_Policy::LRU;
  size_t cache_size = 1024 * 1024 * 1;
};

}
