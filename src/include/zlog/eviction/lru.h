#pragma once
#include<string>
#include<list>
#include<unordered_map>
#include"zlog/eviction.h"

namespace zlog{
    class Cache; // Forward declaration FIX
    class LRU: public Eviction{


        public:

            LRU(int64_t c_size, Cache* c_ref){
                cache_size = c_size;
                cache_ref = c_ref;
                //hit_count = 0;                
            }
            ~LRU();
            
            int cache_get_hit(uint64_t* pos) override;
            int cache_get_miss(uint64_t pos) override;
            int cache_put_miss(uint64_t pos) override;
            uint64_t get_evicted() override;
           // int hit_count;

        private:
            std::unordered_map<uint64_t, std::list<uint64_t>::iterator> eviction_hash_map;
            std::list<uint64_t> eviction_list;
            Cache* cache_ref;
            size_t cache_size;
    };
}