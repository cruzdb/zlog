#ifndef ZLOG_KVSTORE_DB_H
#define ZLOG_KVSTORE_DB_H
#include <cassert>
#include <deque>
#include <set>
#include <iostream>
#include <memory>
#include <condition_variable>
#include <stack>
#include <thread>
#include <mutex>
#include <unordered_map>
#include <vector>
#include "kvstore/kvstore.pb.h"
#include "node.h"
#include "transaction_impl.h"
#include "node_cache.h"
#include "snapshot.h"
#include "iterator_impl.h"
#include "zlog/db.h"
#include "zlog/log.h"

std::ostream& operator<<(std::ostream& out, const NodeRef& n);
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
    return new Snapshot(this, root_, root_pos_, root_desc_);
  }

  void ReleaseSnapshot(Snapshot *snapshot) {
    delete snapshot;
  }

  Iterator *NewIterator(Snapshot *snapshot) {
    return new IteratorImpl(snapshot);
  }

 private:
  friend class TransactionImpl;
  friend class NodeCache;
  friend class NodePtr;
  friend class IteratorTraceApplier;

  void write_dot_recursive(std::ostream& out, uint64_t rid,
      NodeRef node, uint64_t& nullcount, bool scoped);
  void write_dot_null(std::ostream& out, NodeRef node, uint64_t& nullcount);
  void write_dot_node(std::ostream& out, NodeRef parent,
      NodePtr& child, const std::string& dir);
  void _write_dot(std::ostream& out, NodeRef root, uint64_t& nullcount, bool scoped = false);

  int _validate_rb_tree(NodeRef root);
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

  NodeRef fetch(std::vector<std::pair<int64_t, int>>& trace,
      int64_t csn, int offset) {
    return cache_.fetch(trace, csn, offset);
  }

  void UpdateLRU(std::vector<std::pair<int64_t, int>>& trace) {
    cache_.UpdateLRU(trace);
  }

  void print_path(std::ostream& out, std::deque<NodeRef>& path);
  void print_node(NodeRef node);

  // latest committed state
  // TODO: things like root_desc_ are properties of the transaction that
  // created the new root. we should encapsulate this metadata in a structure
  // rather than having it float around freely here.
  NodePtr root_;
  uint64_t root_pos_;
  std::vector<std::string> root_desc_;

  std::mutex lock_;

  zlog::Log *log_;

  NodeCache cache_;

  bool stop_;

  // TODO: how is this initialized?
  static uint64_t root_id_;

  // current transaction handling
  TransactionImpl *cur_txn_;
  std::thread txn_finisher_;
  void TransactionFinisher();
  std::condition_variable txn_finisher_cond_;
};

#endif
