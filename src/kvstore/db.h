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
  Snapshot(const NodeRef root, uint64_t seq) :
    root(root), seq(seq)
  {}

  const NodeRef root;
  const uint64_t seq;
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
    std::lock_guard<std::mutex> l(lock_);
    return Snapshot(root_, root_pos_);
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
  void write_dot_history(std::ostream& out,
      std::vector<Snapshot>& snapshots);

  size_t log_append(std::string blob);
  size_t log_tail();
  std::vector<std::string> log();
  std::string log_read(ssize_t pos);

  bool CommitResult(uint64_t pos);

 private:

  void print_path(std::ostream& out, std::deque<NodeRef>& path);
  void print_node(NodeRef node);

  // only committed states (root, log position)
  // std::map<uint64_t, NodeRef> roots_;
  NodeRef root_;
  uint64_t root_pos_;
  std::mutex lock_;

  // fake/simulated log
  std::vector<std::string> log_;
  std::condition_variable log_cond_;
  std::mutex log_lock_;

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
