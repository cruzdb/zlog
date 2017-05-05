#ifndef ZLOG_KVSTORE_SNAPSHOT_H
#define ZLOG_KVSTORE_SNAPSHOT_H
#include <cstdint>
#include <string>
#include <vector>
#include "node.h"

class Snapshot {
 public:
  Snapshot(DBImpl *db, const NodePtr root) :
    db(db), root(root)
  {}

  DBImpl *db;
  NodePtr root;
};

#endif
