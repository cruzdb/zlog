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
#include "backend.h"
#include "zlog/db.h"

std::ostream& operator<<(std::ostream& out, const NodeRef& n);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::NodePtr& p);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::Node& n);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::Intention& i);

class DBImpl : public DB {
 public:
  explicit DBImpl(Backend *be);
  ~DBImpl();

  Transaction *BeginTransaction();

  Snapshot *GetSnapshot() {
    std::lock_guard<std::mutex> l(lock_);
    return new Snapshot(root_, root_pos_, root_desc_);
  }

  Iterator *NewIterator(Snapshot *snapshot) {
    return new IteratorImpl(snapshot);
  }

 private:
  friend class TransactionImpl;
  friend class NodeCache;

  void write_dot_recursive(std::ostream& out, uint64_t rid,
      NodeRef node, uint64_t& nullcount, bool scoped);
  void write_dot_null(std::ostream& out, NodeRef node, uint64_t& nullcount);
  void write_dot_node(std::ostream& out, NodeRef parent,
      NodePtr& child, const std::string& dir);
  void _write_dot(std::ostream& out, NodeRef root, uint64_t& nullcount, bool scoped = false);

  int _validate_rb_tree(NodeRef root);
  void validate_rb_tree(NodeRef root);

 public:

  void write_dot(std::ostream& out, bool scoped = false);
  void write_dot_history(std::ostream& out,
      std::vector<Snapshot*>& snapshots);

  bool CommitResult(uint64_t pos);

 private:

  void print_path(std::ostream& out, std::deque<NodeRef>& path);
  void print_node(NodeRef node);

  // latest committed state
  // TODO: things like root_desc_ are properties of the transaction that
  // created the new root. we should encapsulate this metadata in a structure
  // rather than having it float around freely here.
  NodeRef root_;
  uint64_t root_pos_;
  std::vector<std::string> root_desc_;

  std::mutex lock_;

  std::condition_variable log_cond_;
  Backend *be_;

  NodeCache cache_;

  uint64_t last_pos_;
  std::thread log_processor_;
  void process_log_entry();

  volatile bool stop_;

  // polling vs cond var vs hybrid
  std::condition_variable result_cv_;

  std::unordered_map<uint64_t, bool> committed_;

  static uint64_t root_id_;
};

#endif
