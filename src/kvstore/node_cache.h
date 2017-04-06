#ifndef ZLOG_KVSTORE_NODE_CACHE_H
#define ZLOG_KVSTORE_NODE_CACHE_H
#include <unordered_map>
#include <mutex>
#include <utility>
#include <thread>
#include <list>
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
    db_(db)
  {
    stop_ = false;
    vaccum_ = std::thread(&NodeCache::do_vaccum_, this);
  }

  NodePtr CacheIntention(const kvstore_proto::Intention& i,
      uint64_t pos);

  NodeRef fetch(int64_t csn, int offset);

  void Stop() {
    lock_.lock();
    stop_ = true;
    lock_.unlock();
    vaccum_.join();
  }

  void SubmitTrace(std::vector<std::pair<int64_t, int>>& trace) {
    std::lock_guard<std::mutex> l(lock_);
    traces_.push_front(trace);
  }

 private:
  DBImpl *db_;
  std::mutex lock_;

  struct entry {
    NodeRef node;
    std::list<std::pair<uint64_t, int>>::iterator lru_iter;
  };

  std::unordered_map<std::pair<uint64_t, int>, entry, pair_hash> nodes_;
  std::list<std::pair<uint64_t, int>> nodes_lru_;

  std::list<std::vector<std::pair<int64_t, int>>> traces_;

  void ResolveNodePtr(NodePtr& ptr);

  NodeRef deserialize_node(const kvstore_proto::Intention& i,
      uint64_t pos, int index);

  std::thread vaccum_;
  void do_vaccum_();
  bool stop_;
};

#endif
