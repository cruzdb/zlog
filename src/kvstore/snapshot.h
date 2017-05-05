#ifndef ZLOG_KVSTORE_SNAPSHOT_H
#define ZLOG_KVSTORE_SNAPSHOT_H
#include <cstdint>
#include <string>
#include <vector>
#include "node.h"

class Snapshot {
 public:
  Snapshot(DBImpl *db, const NodePtr root, uint64_t seq) :
    db(db), root(root), seq(seq)
  {}

  DBImpl *db;
  NodePtr root;
  const uint64_t seq;
};

#endif
