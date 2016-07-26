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
#include "kvstore.pb.h"
#include "node.h"
#include "transaction.h"
#include "node_cache.h"

std::ostream& operator<<(std::ostream& out, const NodeRef& n);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::NodePtr& p);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::Node& n);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::Intention& i);

class Snapshot {
 public:
  Snapshot(const NodeRef root) :
    root(root)
  {}

  const NodeRef root;
};

class DB {
 public:
  DB();
  DB(std::vector<std::string> log);

  ~DB();

  Transaction BeginTransaction();

  std::set<std::string> stl_set();
  std::set<std::string> stl_set(Snapshot snapshot);

  Snapshot GetSnapshot() {
    auto root = roots_.crbegin();
    assert(root != roots_.crend());
    return Snapshot(root->second);
  }

 private:
  friend class Transaction;

  void write_dot_recursive(std::ostream& out, uint64_t rid,
      NodeRef node, uint64_t& nullcount, bool scoped);
  void write_dot_null(std::ostream& out, NodeRef node, uint64_t& nullcount);
  void write_dot_node(std::ostream& out, NodeRef parent,
      NodePtr& child, const std::string& dir);
  void _write_dot(std::ostream& out, NodeRef root, uint64_t& nullcount, bool scoped = false);

  int _validate_rb_tree(NodeRef root);

 public:
  bool validate_rb_tree(bool all = false);

  void write_dot(std::ostream& out, bool scoped = false);
  void write_dot_history(std::ostream& out);

  size_t log_append(std::string blob);
  size_t log_tail();
  std::vector<std::string> log();
  std::string log_read(size_t pos);

  bool CommitResult(uint64_t pos);

 private:

  void print_path(std::deque<NodeRef>& path);
  void print_node(NodeRef node);

  // only committed states (root, log position)
  std::map<uint64_t, NodeRef> roots_;

  // fake/simulated log
  std::vector<std::string> log_;
  std::condition_variable log_cond_;
  std::mutex log_lock_;

  NodeCache cache_;

  uint64_t last_pos_;
  std::thread log_processor_;
  void process_log_entry();

  std::mutex lock_;

  volatile bool stop_;

  // polling vs cond var vs hybrid
  std::condition_variable result_cv_;

  std::unordered_map<uint64_t, bool> committed_;

  static uint64_t root_id_;
};

#endif
