#ifndef ZLOG_KVSTORE_DB_H
#define ZLOG_KVSTORE_DB_H
#include <cassert>
#include <condition_variable>
#include <deque>
#include <iostream>
#include <memory>
#include <mutex>
#include <set>
#include <stack>
#include <thread>
#include <unordered_map>
#include <vector>

#include "iterator_impl.h"
#include "kvstore/kvstore.pb.h"
#include "node.h"
#include "node_cache.h"
#include "snapshot.h"
#include "transaction_impl.h"
#include "zlog/db.h"
#include "zlog/log.h"

std::ostream& operator<<(std::ostream& out, const SharedNodeRef& n);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::NodePtr& p);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::Node& n);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::Intention& i);

class DBImpl : public DB {
 public:
  explicit DBImpl(zlog::Log *log);
  ~DBImpl();

  Transaction *BeginTransaction();

  Snapshot *GetSnapshot() {
    std::lock_guard<std::mutex> l(lock_);
    return new Snapshot(this, root_);
  }

  void ReleaseSnapshot(Snapshot *snapshot) {
    delete snapshot;
  }

  Iterator *NewIterator(Snapshot *snapshot) {
    return new IteratorImpl(snapshot);
  }

  int RestoreFromLog();

 private:
  friend class TransactionImpl;
  friend class NodeCache;
  friend class NodePtr;
  friend class IteratorTraceApplier;

  void write_dot_recursive(std::ostream& out, int64_t rid,
      SharedNodeRef node, uint64_t& nullcount, bool scoped);
  void write_dot_null(std::ostream& out, SharedNodeRef node, uint64_t& nullcount);
  void write_dot_node(std::ostream& out, SharedNodeRef parent,
      NodePtr& child, const std::string& dir);
  void _write_dot(std::ostream& out, SharedNodeRef root, uint64_t& nullcount, bool scoped = false);

  int _validate_rb_tree(SharedNodeRef root);
  void validate_rb_tree(NodePtr root);

 public:

  void write_dot(std::ostream& out, bool scoped = false);
  void write_dot_history(std::ostream& out,
      std::vector<Snapshot*>& snapshots);
  void validate() {
    const auto snapshot = root_;
    validate_rb_tree(snapshot);
  }

 public:
  void CompleteTransaction(TransactionImpl *txn);
  void AbortTransaction(TransactionImpl *txn);

 private:

  SharedNodeRef fetch(std::vector<std::pair<int64_t, int>>& trace,
      int64_t csn, int offset) {
    return cache_.fetch(trace, csn, offset);
  }

  void UpdateLRU(std::vector<std::pair<int64_t, int>>& trace) {
    cache_.UpdateLRU(trace);
  }

  void print_path(std::ostream& out, std::deque<SharedNodeRef>& path);
  void print_node(SharedNodeRef node);

  std::mutex lock_;
  zlog::Log *log_;
  NodeCache cache_;
  bool stop_;

  // counter to generate a unique root id for in-flight transactions.
  // committed transactions use their position in the log as a root id, and
  // this counter is always negative to produce non-conflicting values.
  int64_t root_id_;

  // tree from last tranascation
  NodePtr root_;

  // transaction handling
  TransactionImpl *cur_txn_;
  std::thread txn_finisher_;
  void TransactionFinisher();
  std::condition_variable txn_finisher_cond_;
};

#endif
