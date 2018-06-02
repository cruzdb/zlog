//#include"zlog/eviction.h"
#include"zlog/eviction/lru.h"
#include"zlog/cache.h"
//#include<list>

namespace zlog{

LRU::~LRU(){}

int LRU::cache_get_hit(uint64_t* pos){
    auto it = eviction_hash_map[*pos];
    eviction_list.splice(eviction_list.begin(), eviction_list, it);
    // hit_count++;
    // std::cout << hit_count << std::endl;
    
    return 0;
}

int LRU::cache_get_miss(uint64_t pos){
    return 0;
}

int LRU::cache_put_miss(uint64_t pos){
    eviction_list.push_front(pos);
    eviction_hash_map[pos] = eviction_list.begin();

    if(eviction_hash_map.size() > cache_size){

        auto r = eviction_list.back();
        eviction_hash_map.erase(r);
        cache_ref->cache_map.erase(r);
        eviction_list.pop_back();
    }


    return 0;
}

uint64_t LRU::get_evicted(){
    auto r = eviction_list.back();
    eviction_hash_map.erase(r);
    eviction_list.pop_back();

    return r;
}
}