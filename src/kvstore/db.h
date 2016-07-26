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
  DB(std::vector<std::string> db);

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

  std::vector<std::string> get_db() {
    return db_;
  }

  size_t db_log_append(std::string blob);

  bool CommitResult(uint64_t pos);

 private:

  void print_path(std::deque<NodeRef>& path);
  void print_node(NodeRef node);

  // only committed states (root, log position)
  std::map<uint64_t, NodeRef> roots_;

  std::vector<std::string> db_;
  std::map<std::pair<uint64_t, int>, NodeRef> node_cache_;

  uint64_t last_pos_;
  std::thread log_processor_;
  void process_log_entry();

  std::mutex lock_;

  volatile bool stop_;

  std::condition_variable cv_;
  std::condition_variable result_cv_;

  std::unordered_map<uint64_t, bool> committed_;

  void node_cache_get_(NodePtr& ptr) {
    assert(ptr.ref == nullptr);
#if 0
    std::cerr << "node_cache_get_: csn " << ptr.csn << " off " << ptr.offset << std::endl;
#endif
    lock_.lock();
    auto it = node_cache_.find(std::make_pair(ptr.csn, ptr.offset));
    bool cached = it != node_cache_.end();
    if (cached) {
      ptr.ref = it->second;
      lock_.unlock();
      return;
    }

    // read and deserialize intention from log
    std::string snapshot = db_.at(ptr.csn);
    lock_.unlock();
    kvstore_proto::Intention i;
    assert(i.ParseFromString(snapshot));
    assert(i.IsInitialized());

    const kvstore_proto::Node& n = i.tree(ptr.offset);

    // here we use rid == log offset. itd be nice to have something uniquely
    // generated in memory as a safety net. we can use a csn->rid map to
    // handle this.
    auto nn = std::make_shared<Node>(n.value(), n.red(),
        Node::Nil(), Node::Nil(), ptr.csn);

    nn->field_index = ptr.offset;
    if (!n.left().nil()) {
      nn->left.ref = nullptr;
      nn->left.offset = n.left().off();
      if (n.left().self()) {
        nn->left.csn = ptr.csn;
      } else {
        nn->left.csn = n.left().csn();
      }
    }
    if (!n.right().nil()) {
      nn->right.ref = nullptr;
      nn->right.offset = n.right().off();
      if (n.right().self()) {
        nn->right.csn = ptr.csn;
      } else {
        nn->right.csn = n.right().csn();
      }
    }

    lock_.lock();
    node_cache_.insert(std::make_pair(std::make_pair(ptr.csn, ptr.offset), nn));
    lock_.unlock();

    ptr.ref = nn;
  }

  static uint64_t root_id_;
};

#endif
