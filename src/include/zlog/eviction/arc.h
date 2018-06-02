#pragma once
#include<string>
#include<list>
#include<unordered_map>
#include"zlog/eviction.h"

namespace zlog{
    class Cache; // Forward declaration FIX
    class ARC: public Eviction{


        public:

            ARC(int64_t cache_size, Cache* c_ref){
                cache_ref = c_ref;
                arc_c = cache_size;
                //hit_count = 0;
            }
            ~ARC();
            
            int cache_get_hit(uint64_t* pos) override;
            int cache_get_miss(uint64_t pos) override;
            int cache_put_miss(uint64_t pos) override;
            uint64_t get_evicted() override;
            //int hit_count;

        private:
            double get_delta_1();
            double get_delta_2();
            int replace(uint64_t pos);
            std::unordered_map<uint64_t, std::list<uint64_t>::iterator> t1_hash_map;
            std::unordered_map<uint64_t, std::list<uint64_t>::iterator> b1_hash_map;
            std::unordered_map<uint64_t, std::list<uint64_t>::iterator> t2_hash_map;
            std::unordered_map<uint64_t, std::list<uint64_t>::iterator> b2_hash_map;
            std::list<uint64_t> t1_eviction_list;
            std::list<uint64_t> b1_eviction_list;
            std::list<uint64_t> t2_eviction_list;
            std::list<uint64_t> b2_eviction_list;
            size_t arc_c;
            double arc_p;
            Cache* cache_ref;
    };
}