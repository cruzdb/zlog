#include"zlog/eviction/arc.h"
#include<algorithm>
#include<iostream>
#include"zlog/cache.h"

namespace zlog{

ARC::~ARC(){}

int ARC::cache_get_hit(uint64_t* pos){
    
    // std::cout << "read: " << *pos << std::endl;
    

    if(t1_hash_map.find(*pos) != t1_hash_map.end()){
        // std::cout << "hit t1 " << std::endl;
        auto it = t1_hash_map[*pos];
        t2_eviction_list.splice(t2_eviction_list.begin(), t1_eviction_list, it);
        t2_hash_map[*pos] = it;
        t1_hash_map.erase(*pos);

    }else if(t2_hash_map.find(*pos) != t2_hash_map.end()){
        // std::cout << "hit t2 " << std::endl;
        auto it = t2_hash_map[*pos];
        t2_eviction_list.splice(t2_eviction_list.begin(), t2_eviction_list, it);

    }else{
        return -1;
    }


    // std::cout << "t1 hash: " << t1_hash_map.size() << std::endl;
    // std::cout << "t1 list: " << t1_eviction_list.size() << std::endl;
    // std::cout << "t2 hash: " << t2_hash_map.size() << std::endl;
    // std::cout << "t2 list: " << t2_eviction_list.size() << std::endl;
    // std::cout << "b1 hash: " << b1_hash_map.size() << std::endl;
    // std::cout << "b1 list: " << b1_eviction_list.size() << std::endl;
    // std::cout << "b2 hash: " << b2_hash_map.size() << std::endl;
    // std::cout << "b2 list: " << b2_eviction_list.size() << std::endl;
    
    // std::cout << "------------------------------------------------" << std::endl;
    // hit_count++;
    // std::cout << hit_count << std::endl;
    return 0;
}

int ARC::cache_get_miss(uint64_t pos){
   return 0;
}

int ARC::cache_put_miss(uint64_t pos){
      if(b1_hash_map.find(pos) != b1_hash_map.end()){
        // std::cout << "hit b1 " << std::endl;
          
        auto it = b1_hash_map[pos];
        
        arc_p = std::min(arc_p + get_delta_1(), (double)arc_c);
        replace(pos);
        t2_eviction_list.splice(t2_eviction_list.begin(), b1_eviction_list, it);
        t2_hash_map[pos] = it;
        b1_hash_map.erase(pos);

    }else if(b2_hash_map.find(pos) != b2_hash_map.end()){
        // std::cout << "hit b2 " << std::endl;
        
        auto it = b2_hash_map[pos];
        arc_p = std::max(arc_p - get_delta_2(), 0.0);
        replace(pos);
        t2_eviction_list.splice(t2_eviction_list.begin(), b2_eviction_list, it);
        t2_hash_map[pos] = it;
        b2_hash_map.erase(pos);
    }else{
        // std::cout << "cache miss " << std::endl;
        
        if(t1_hash_map.size() + b1_hash_map.size() >= arc_c){
            if(t1_hash_map.size() < arc_c){
                auto r = b1_eviction_list.back();
                b1_hash_map.erase(r);
                b1_eviction_list.pop_back();
                replace(pos);
            }else{
                auto r = t1_eviction_list.back();
                t1_hash_map.erase(r);
                t1_eviction_list.pop_back();
                cache_ref->cache_map.erase(r);
            }
        }else{
            if(t1_hash_map.size() + b1_hash_map.size() + t2_hash_map.size() + b2_hash_map.size() >= arc_c){
                if(t1_hash_map.size() + b1_hash_map.size() + t2_hash_map.size() + b2_hash_map.size() >= 2 * arc_c){
                    auto r = b2_eviction_list.back();
                    b2_hash_map.erase(r);
                    b2_eviction_list.pop_back();
                }
                replace(pos);
            }
        }
        t1_eviction_list.push_front(pos);
        t1_hash_map[pos] = t1_eviction_list.begin();
    }


    //  std::cout << "put: " << pos << std::endl;

    // std::cout << "t1 hash: " << t1_hash_map.size() << std::endl;
    // std::cout << "t1 list: " << t1_eviction_list.size() << std::endl;
    // std::cout << "t2 hash: " << t2_hash_map.size() << std::endl;
    // std::cout << "t2 list: " << t2_eviction_list.size() << std::endl;
    // std::cout << "b1 hash: " << b1_hash_map.size() << std::endl;
    // std::cout << "b1 list: " << b1_eviction_list.size() << std::endl;
    // std::cout << "b2 hash: " << b2_hash_map.size() << std::endl;
    // std::cout << "b2 list: " << b2_eviction_list.size() << std::endl;
    
    // std::cout << "------------------------------------------------" << std::endl;
    return 0;
}

uint64_t ARC::get_evicted(){
    return -1;
}

double ARC::get_delta_1(){
    if(b1_hash_map.size() >= b2_hash_map.size()){
        return 1.0;
    }else{
        return (double)(b2_hash_map.size()) / (double)(b1_hash_map.size());
    }
}

double ARC::get_delta_2(){
    if(b2_hash_map.size() >= b1_hash_map.size()){
        return 1.0;
    }else{
        return (double)(b1_hash_map.size()) / (double)(b2_hash_map.size());
    }
}

int ARC::replace(uint64_t pos){
    if(t1_hash_map.size() > 0 && (t1_hash_map.size() > arc_p || 
    (b2_hash_map.find(pos) != b2_hash_map.end() && t1_hash_map.size() <= arc_p)
    )){

        auto r = t1_eviction_list.back();
        t1_hash_map.erase(r);
        t1_eviction_list.pop_back();
        
        cache_ref->cache_map.erase(r);

        b1_eviction_list.push_front(r);
        b1_hash_map[r] = b1_eviction_list.begin();

    }else{
        auto r = t2_eviction_list.back();
        t2_hash_map.erase(r);
        t2_eviction_list.pop_back();
        
        cache_ref->cache_map.erase(r);

        b2_eviction_list.push_front(r);
        b2_hash_map[r] = b2_eviction_list.begin();
    }
    return 0;
}

}