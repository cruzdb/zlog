#ifndef ZLOG_KVSTORE_NODE_CACHE_H
#define ZLOG_KVSTORE_NODE_CACHE_H
#include <map>
#include <mutex>
#include <utility>
#include "node.h"
#include "kvstore/kvstore.pb.h"

class DBImpl;

class NodeCache {
 public:
  explicit NodeCache(DBImpl *db) :
    db_(db)
  {}

  NodeRef CacheIntention(const kvstore_proto::Intention& i,
      uint64_t pos);

 private:
  DBImpl *db_;
  std::mutex lock_;
  std::map<std::pair<uint64_t, int>, NodeRef> nodes_;

  void ResolveNodePtr(NodePtr& ptr);

  NodeRef deserialize_node(const kvstore_proto::Intention& i,
      uint64_t pos, int index);
};

#endif
