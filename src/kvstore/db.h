#ifndef ZLOG_KVSTORE_DB_H
#define ZLOG_KVSTORE_DB_H
#include <cassert>
#include <deque>
#include <set>
#include <iostream>
#include <memory>
#include <stack>
#include <vector>
#include "kvstore.pb.h"

struct Node;
using NodeRef = std::shared_ptr<Node>;

/*
 *
 */
struct NodePtr {
  NodeRef ref;
  int64_t csn;
  int offset;

  NodePtr() : NodePtr(nullptr) {}

  explicit NodePtr(NodeRef ref) :
    ref(ref), csn(-1), offset(-1)
  {}
};

/*
 *
 */
struct Node {
  std::string elem;
  bool red;
  NodePtr left;
  NodePtr right;

  uint64_t rid;
  int field_index;

  Node(std::string elem, bool red, NodeRef lr, NodeRef rr, uint64_t rid) :
    elem(elem), red(red), left(lr), right(rr), rid(rid), field_index(-1)
  {}
};

std::ostream& operator<<(std::ostream& out, const NodeRef& n);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::NodePtr& p);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::Node& n);
std::ostream& operator<<(std::ostream& out, const kvstore_proto::Intention& i);

class DB {
 public:
  DB();

  void insert(std::string elem);

  std::set<std::string> stl_set();
  std::set<std::string> stl_set(size_t root);

  size_t num_roots() {
    return roots_.size();
  }

  static NodeRef& Nil() {
    static NodeRef node = std::make_shared<Node>(
        "", false, nullptr, nullptr, 0);
    return node;
  }

 private:
  void serialize_node(kvstore_proto::Node *n, NodeRef node, uint64_t rid, int field_index);
  void serialize_intention_recursive(kvstore_proto::Intention& i, uint64_t rid, NodeRef node, int& field_index);
  void serialize_intention(kvstore_proto::Intention& i, NodeRef node);

  void set_intention_self_csn_recursive(uint64_t rid, NodeRef node, uint64_t pos);
  void set_intention_self_csn(NodeRef root, uint64_t pos);

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

  void restore(DB& other, int pos = -1) {
    // clear all state
    roots_.clear();
    db_.clear();
    node_cache_.clear();

    // copy just the database
    db_ = other.db_;

    // start from end or specific pos
    assert(node_cache_.empty());
    assert(db_.size());
    if (pos == -1)
      pos = db_.size() - 1;
    std::string snapshot = db_.at(pos);

    kvstore_proto::Intention i;
    assert(i.ParseFromString(snapshot));
    assert(i.IsInitialized());

    if (i.tree_size() == 0)
      roots_.push_back(DB::Nil());

    uint64_t rid = pos;
    for (int idx = 0; idx < i.tree_size(); idx++) {
      const kvstore_proto::Node& n = i.tree(idx);
      auto nn = std::make_shared<Node>(n.value(), n.red(), DB::Nil(), DB::Nil(), rid);
      nn->field_index = idx;
      if (!n.left().nil()) {
        nn->left.ref = nullptr;
        nn->left.offset = n.left().off();
        if (n.left().self()) {
          nn->left.csn = pos;
        } else {
          nn->left.csn = n.left().csn();
        }
      }
      if (!n.right().nil()) {
        nn->right.ref = nullptr;
        nn->right.offset = n.right().off();
        if (n.right().self()) {
          nn->right.csn = pos;
        } else {
          nn->right.csn = n.right().csn();
        }
      }

      std::cerr << "restore: node_cache insert: pos " << pos
        << " idx  " << idx
        << " nn.left.nil " << (nn->left.ref == DB::Nil())
        << " nn.left.off " << nn->left.offset
        << " nn.right.nil " << (nn->right.ref == DB::Nil())
        << " nn.right.off " << nn->right.offset
        << std::endl;

      node_cache_.insert(std::make_pair(std::make_pair(pos, idx), nn));

      // FIXME: adding this root is unnatural we are really building a view
      if (idx == (i.tree_size() - 1))
        roots_.push_back(nn);
    }
  }

 private:
  NodeRef copy_node(NodeRef node, uint64_t rid) const {

    if (node == DB::Nil())
      return DB::Nil();

    auto n = std::make_shared<Node>(node->elem, node->red,
        node->left.ref, node->right.ref, rid);

    //assert(node->left.ref == DB::Nil() || node->left.offset >= 0);

    n->left.csn = node->left.csn;
    n->left.offset = node->left.offset;

    n->right.csn = node->right.csn;
    n->right.offset = node->right.offset;

    std::cerr << "copy_node: src " << node << " dst " << n << std::endl;

    return n;
  }

  NodeRef insert_recursive(std::deque<NodeRef>& path,
      std::string elem, NodeRef& node, uint64_t rid);

  template<typename ChildA, typename ChildB>
  void insert_balance(NodeRef& parent, NodeRef& nn,
      std::deque<NodeRef>& path, ChildA, ChildB, NodeRef& root,
      uint64_t rid);

  template <typename ChildA, typename ChildB >
  NodeRef rotate(NodeRef parent, NodeRef child,
      ChildA child_a, ChildB child_b, NodeRef& root,
      uint64_t rid);

  void print_path(std::deque<NodeRef>& path);
  void print_node(NodeRef node);

  std::deque<NodeRef> roots_;
  std::vector<std::string> db_;
  std::map<std::pair<uint64_t, int>, NodeRef> node_cache_;

  void node_cache_get_(NodePtr& ptr) {
    assert(ptr.ref == nullptr);
    std::cerr << "node_cache_get_: csn " << ptr.csn << " off " << ptr.offset << std::endl;
    auto it = node_cache_.find(std::make_pair(ptr.csn, ptr.offset));
    bool cached = it != node_cache_.end();
    if (cached) {
      ptr.ref = it->second;
      return;
    }

    // read and deserialize intention from log
    std::string snapshot = db_.at(ptr.csn);
    kvstore_proto::Intention i;
    assert(i.ParseFromString(snapshot));
    assert(i.IsInitialized());

    const kvstore_proto::Node& n = i.tree(ptr.offset);

    // here we use rid == log offset. itd be nice to have something uniquely
    // generated in memory as a safety net. we can use a csn->rid map to
    // handle this.
    auto nn = std::make_shared<Node>(n.value(), n.red(),
        DB::Nil(), DB::Nil(), ptr.csn);

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

    node_cache_.insert(std::make_pair(std::make_pair(ptr.csn, ptr.offset), nn));

    ptr.ref = nn;
  }

  static uint64_t root_id_;

  static NodePtr& left(NodeRef n) { return n->left; };
  static NodePtr& right(NodeRef n) { return n->right; };

  static NodeRef pop_front(std::deque<NodeRef>& d) {
    auto front = d.front();
    d.pop_front();
    return front;
  }
};

#endif
