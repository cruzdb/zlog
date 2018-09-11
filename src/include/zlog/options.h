#pragma once
#include <memory>
#include <string>
#include <vector>
#include "eviction.h"
#include "statistics.h"

namespace zlog {

class Statistics;

struct Options {
  int width = 10;
  int entries_per_object = 200;

  Statistics* statistics = nullptr;
  std::vector<std::string> http;
  
  //cache options
  zlog::Eviction::Eviction_Policy eviction = zlog::Eviction::Eviction_Policy::LRU;
  size_t cache_size = 1024 * 1024 * 1;
};

}
