#pragma once
#include<string>
#include<sstream>
#include<iostream>
#include<unordered_map>
#include<mutex>
#include"zlog/eviction/lru.h"
#include"zlog/eviction/arc.h"
#include"zlog/options.h"
#include"zlog/mempool/mempool.h"
#include"zlog/slice.h"
#include"../../monitoring/statistics.h"

namespace zlog{
class Cache{
    public:
        Cache(const zlog::Options& ops) : options(ops){


            current_cache_use = 0;

            switch(options.eviction){
                case zlog::Eviction::Eviction_Policy::LRU:
                    eviction = new LRU(options.cache_size, this);
                break;
                case zlog::Eviction::Eviction_Policy::ARC:
                    eviction = new ARC(options.cache_size, this);
                break;
                default:
                    eviction = new LRU(options.cache_size, this);
                    std::cout << "Eviction policy not implemented. Using default: LRU" << std::endl;   
                break;
            }

        }
        ~Cache();

        int put(uint64_t pos, const Slice& data);    
        int get(uint64_t* pos, std::string* data);
        int remove(uint64_t* pos);

        std::unordered_map<uint64_t, zlog_mempool::cache::string> cache_map; //FIX


    private:
        zlog::Eviction* eviction;
        const zlog::Options& options;
        int64_t current_cache_use;
        std::mutex mut;

};
}