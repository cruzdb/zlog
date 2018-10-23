#include<iostream>
#include<string>
#include<unordered_map>
#include<tuple>
#include<iterator>
#include"include/zlog/eviction.h"
#include"include/zlog/cache.h"

namespace zlog{

Cache::~Cache(){}

int Cache::put(uint64_t pos, const std::string& data){
  int ret = 0;
  mut.lock();
  if(options.cache_size > 0 && data.size() < options.cache_size && cache_map.find(pos) == cache_map.end()){ 
    eviction->cache_put_miss(pos);
    zlog_mempool::cache::string pool_data(data.data(), data.size());
    cache_map[pos] = zlog_mempool::cache::string(pool_data);
  }else{
    ret = -1;
  }
  mut.unlock();
  return ret;
}

int Cache::get(uint64_t* pos, std::string* data){
  #ifdef WITH_STATS
  RecordTick(options.statistics, CACHE_REQS);
  #endif
  auto map_it = cache_map.find(*pos);
  int ret = 0;       
  mut.lock(); 
  if(map_it != cache_map.end()){
    data->assign((map_it->second).data(), (map_it->second).size());
    eviction->cache_get_hit(pos);
  }else{
    #ifdef WITH_STATS
    RecordTick(options.statistics, CACHE_MISSES);
    #endif
    ret = 1;
  }
  mut.unlock();
  return ret;
}

int Cache::remove(uint64_t* pos){
  if(cache_map.erase(*pos) > 0){
    return 0;    
  }
  return 1;
}
}
