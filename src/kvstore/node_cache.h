#ifndef ZLOG_KVSTORE_NODE_CACHE_H
#define ZLOG_KVSTORE_NODE_CACHE_H
#include <unordered_map>
#include <mutex>
#include <utility>
#include <thread>
#include <list>
#include <condition_variable>
#include "node.h"
#include "kvstore/kvstore.pb.h"

class DBImpl;

template <class T>
inline void hash_combine(std::size_t& seed, const T& v)
{
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

struct pair_hash {
  template <class T1, class T2>
  std::size_t operator () (const std::pair<T1,T2> &p) const {
    auto h1 = std::hash<T1>{}(p.first);
    auto h2 = std::hash<T2>{}(p.second);
    size_t hval = 0;
    hash_combine(hval, h1);
    hash_combine(hval, h2);
    return hval;
  }
};

class NodeCache {
 public:
  explicit NodeCache(DBImpl *db) :
    db_(db),
    stop_(false),
    used_bytes_(0)
  {
    vaccum_ = std::thread(&NodeCache::do_vaccum_, this);
  }

  NodePtr CacheIntention(const kvstore_proto::Intention& i,
      uint64_t pos);

  NodeRef fetch(std::vector<std::pair<int64_t, int>>& trace,
      int64_t csn, int offset);

  void Stop() {
    lock_.lock();
    stop_ = true;
    lock_.unlock();
    cond_.notify_one();
    vaccum_.join();
  }

  void UpdateLRU(std::vector<std::pair<int64_t, int>>& trace) {
    if (!trace.empty()) {
      std::lock_guard<std::mutex> l(lock_);
      traces_.emplace_front();
      traces_.front().swap(trace);
      cond_.notify_one();
    }
  }

 private:
  DBImpl *db_;
  std::mutex lock_;
  size_t used_bytes_;

  struct entry {
    NodeRef node;
    std::list<std::pair<uint64_t, int>>::iterator lru_iter;
  };

  size_t UsedBytes() const {
    return used_bytes_;
  }

  std::unordered_map<std::pair<uint64_t, int>, entry, pair_hash> nodes_;
  std::list<std::pair<uint64_t, int>> nodes_lru_;

  std::list<std::vector<std::pair<int64_t, int>>> traces_;

  void ResolveNodePtr(NodePtr& ptr);

  NodeRef deserialize_node(const kvstore_proto::Intention& i,
      uint64_t pos, int index);

  std::thread vaccum_;
  std::condition_variable cond_;
  void do_vaccum_();
  bool stop_;
};

#endif
