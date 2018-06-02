#pragma once
#include<string>

namespace zlog{

    class Eviction{


        public:

            enum Eviction_Policy{
                LRU,
                ARC
            };

            virtual ~Eviction(){};

            virtual int cache_get_hit(uint64_t* pos) = 0;
            virtual int cache_get_miss(uint64_t pos) = 0;
            virtual int cache_put_miss(uint64_t pos) = 0;
            virtual uint64_t get_evicted() = 0;
    };
}