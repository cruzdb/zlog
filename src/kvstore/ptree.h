#ifndef ZLOG_KVSTORE_PTREE_H
#define ZLOG_KVSTORE_PTREE_H
#include <cassert>
#include <deque>
#include <set>
#include <iostream>
#include <memory>
#include <stack>
#include <vector>
#include "kvstore.pb.h"

template<typename T>
struct Node;

template<typename T>
using NodeRef = std::shared_ptr<Node<T>>;

/*
 *
 */
template<typename T>
struct NodePtr {
  NodeRef<T> ref;
  int64_t csn;
  int offset;

  NodePtr() : NodePtr(nullptr) {}

  explicit NodePtr(NodeRef<T> ref) :
    ref(ref), csn(-1), offset(-1)
  {}
};

/*
 *
 */
template<typename T>
struct Node {
  T elem;
  bool red;
  NodePtr<T> left;
  NodePtr<T> right;

  uint64_t rid;
  int field_index;

  Node(T elem, bool red, NodeRef<T> lr, NodeRef<T> rr, uint64_t rid) :
    elem(elem), red(red), left(lr), right(rr), rid(rid), field_index(-1)
  {}

  static NodeRef<T>& nil() {
    static NodeRef<T> node = std::make_shared<Node<T>>(
        T(), false, nullptr, nullptr, 0);
    return node;
  }
};

template<typename T>
std::ostream& operator<<(std::ostream& out, const NodeRef<T>& n)
{
  out << "node(" << n.get() << "):" << n->elem << ": ";
  out << (n->red ? "red " : "blk ");
  out << "fi " << n->field_index << " ";
  out << "left=[p" << n->left.csn << ",o" << n->left.offset << ",";
  out << n->left.ref.get() << "] ";
  out << "right=[p" << n->right.csn << ",o" << n->right.offset << ",";
  out << n->right.ref.get() << "] ";
  return out;
}

std::ostream& operator<<(std::ostream& out, const kvstore_proto::NodePtr& p)
{
  out << "[n" << p.nil() << ",s" << p.self()
    << ",p" << p.csn() << ",o" << p.off() << "]";
  return out;
}

std::ostream& operator<<(std::ostream& out, const kvstore_proto::Node& n)
{
  out << "val " << n.value() << " ";
  out << (n.red() ? "red" : "blk") << " ";
  out << "left " << n.left() << " right " << n.right();
  return out;
}

std::ostream& operator<<(std::ostream& out, const kvstore_proto::Intention& i)
{
  out << "- intention tree_size = " << i.tree_size() << std::endl;
  for (int idx = 0; idx < i.tree_size(); idx++) {
    out << "  " << idx << ": " << i.tree(idx) << std::endl;
  }
  return out;
}

template<typename T>
class PTree {
 public:
  explicit PTree(std::vector<std::string> *db);

  PTree<T> insert(T elem);

  std::set<T> stl_set() {
    std::set<T> set;
    NodeRef<T> node = root_;
    if (node == Node<T>::nil())
      return set;
    std::stack<NodeRef<T>> stack;
    stack.push(node);
    while (!stack.empty()) {
      node = stack.top();
      stack.pop();
      auto ret = set.emplace(node->elem);
      assert(ret.second);
      if (node->right.ref != Node<T>::nil()) {
        if (node->right.ref == nullptr)
          node_cache_get_(node->right);
        stack.push(node->right.ref);
      }
      if (node->left.ref != Node<T>::nil()) {
        if (node->left.ref == nullptr)
          node_cache_get_(node->left);
        stack.push(node->left.ref);
      }
    }
    return set;
  }

 private:
  // a node in an intention contains pointers that are:
  //
  // 1. nil
  // 2. targets outside this intention
  // 3. targets within this intention
  // 4. targets within this intention to the newly created node
  //
  // If (1) then csn/off are ignored, so nothing special is required.
  //
  // If (2) then the pointer was copied from a previous version of the tree,
  // in which case the csn/off was also copied over.
  //
  //    NOTE: need ot make sure this is reflected in the balance/rotate logic
  //    so that we aren't JUST copying the shared_ptr.
  //
  // If (3) then the pointer needs to have its csn set to 0 and its offset
  // updated correctly.
  //
  // if (4), then same as (3).

  void serialize_node(kvstore_proto::Node *n, NodeRef<T> node,
      uint64_t rid, int field_index) {

    n->set_red(node->red);
    n->set_value(node->elem);

    assert(node->field_index == -1);
    node->field_index = field_index;
    assert(node->field_index >= 0);

    std::cerr << "serialize_node: " << node << std::endl;

    if (node->left.ref == Node<T>::nil()) {
      n->mutable_left()->set_nil(true);
      n->mutable_left()->set_self(false);
      n->mutable_left()->set_csn(0);
      n->mutable_left()->set_off(0);
      std::cerr << " - serialize_node: left nil" << std::endl;
    } else if (node->left.ref->rid == rid) {
      n->mutable_left()->set_nil(false);
      n->mutable_left()->set_self(true);
      n->mutable_left()->set_csn(0);
      assert(node->left.ref->field_index >= 0);
      n->mutable_left()->set_off(node->left.ref->field_index);
      node->left.offset = node->left.ref->field_index;
      std::cerr << " - serialize_node: left internal csn " <<
        n->mutable_left()->csn() << " off " << n->mutable_left()->off()
        << std::endl;
    } else {
      assert(node->left.ref != nullptr);
      n->mutable_left()->set_nil(false);
      n->mutable_left()->set_self(false);
      n->mutable_left()->set_csn(node->left.csn);
      n->mutable_left()->set_off(node->left.offset);
      std::cerr << " - serialize_node: left external csn " <<
        n->mutable_left()->csn() << " off " << n->mutable_left()->off()
        << std::endl;
    }

    if (node->right.ref == Node<T>::nil()) {
      n->mutable_right()->set_nil(true);
      n->mutable_right()->set_self(false);
      n->mutable_right()->set_csn(0);
      n->mutable_right()->set_off(0);
      std::cerr << " - serialize_node: right nil" << std::endl;
    } else if (node->right.ref->rid == rid) {
      n->mutable_right()->set_nil(false);
      n->mutable_right()->set_self(true);
      n->mutable_right()->set_csn(0);
      assert(node->right.ref->field_index >= 0);
      n->mutable_right()->set_off(node->right.ref->field_index);
      node->right.offset = node->right.ref->field_index;
      std::cerr << " - serialize_node: right internal csn " <<
        n->mutable_right()->csn() << " off " << n->mutable_right()->off()
        << std::endl;
    } else {
      assert(node->right.ref != nullptr);
      n->mutable_right()->set_nil(false);
      n->mutable_right()->set_self(false);
      n->mutable_right()->set_csn(node->right.csn);
      n->mutable_right()->set_off(node->right.offset);
      std::cerr << " - serialize_node: right external csn " <<
        n->mutable_right()->csn() << " off " << n->mutable_right()->off()
        << std::endl;
    }

  }

  void serialize_intention_recursive(kvstore_proto::Intention& i,
      uint64_t rid, NodeRef<T> node, int& field_index) {

    if (node == Node<T>::nil() || node->rid != rid)
      return;

    serialize_intention_recursive(i, rid, node->left.ref, field_index);
    serialize_intention_recursive(i, rid, node->right.ref, field_index);

    // new serialized node in the intention
    kvstore_proto::Node *n = i.add_tree();
    serialize_node(n, node, rid, field_index);
    field_index++;
  }

  void serialize_intention(kvstore_proto::Intention& i, NodeRef<T> node) {
    int field_index = 0;
    serialize_intention_recursive(i, node->rid, node, field_index);
  }

  void set_intention_self_csn_recursive(uint64_t rid,
      NodeRef<T> node, uint64_t pos) {

    if (node == Node<T>::nil() || node->rid != rid)
      return;

    if (node->right.ref != Node<T>::nil() && node->right.ref->rid == rid) {
      node->right.csn = pos;
    }

    if (node->left.ref != Node<T>::nil() && node->left.ref->rid == rid) {
      node->left.csn = pos;
    }

    set_intention_self_csn_recursive(rid, node->right.ref, pos);
    set_intention_self_csn_recursive(rid, node->left.ref, pos);
  }

  void set_intention_self_csn(NodeRef<T> root, uint64_t pos) {
    set_intention_self_csn_recursive(root->rid, root, pos);
  }

  void write_dot_recursive(std::ostream& out, uint64_t rid,
      NodeRef<T> node, uint64_t& nullcount, bool scoped);
  void write_dot_null(std::ostream& out, NodeRef<T> node, uint64_t& nullcount);
  void write_dot_node(std::ostream& out, NodeRef<T> parent,
      NodePtr<T>& child, const std::string& dir);
  void _write_dot(std::ostream& out, uint64_t& nullcount, bool scoped = false);

  int _validate_rb_tree(NodeRef<T> root);

 public:
  bool validate_rb_tree();
  void write_dot(std::ostream& out, bool scoped = false);
  void write_dot(std::ostream& out,
      std::vector<PTree<T>>& versions);

  void restore() {
    assert(node_cache_);
    assert(db_->size());
    int pos = db_->size() - 1;
    std::string snapshot = db_->at(pos);

    kvstore_proto::Intention i;
    assert(i.ParseFromString(snapshot));
    assert(i.IsInitialized());

    uint64_t rid = pos;
    for (int idx = 0; idx < i.tree_size(); idx++) {
      const kvstore_proto::Node& n = i.tree(idx);
      auto nn = std::make_shared<Node<T>>(n.value(), n.red(), Node<T>::nil(), Node<T>::nil(), rid);
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
        << " nn.left.nil " << (nn->left.ref == Node<T>::nil())
        << " nn.left.off " << nn->left.offset
        << " nn.right.nil " << (nn->right.ref == Node<T>::nil())
        << " nn.right.off " << nn->right.offset
        << std::endl;

      node_cache_->insert(std::make_pair(std::make_pair(pos, idx), nn));

      if (idx == (i.tree_size() - 1))
        root_ = nn;
    }
  }

 private:
  NodeRef<T> copy_node(NodeRef<T> node, uint64_t rid) const {

    if (node == Node<T>::nil())
      return Node<T>::nil();

    auto n = std::make_shared<Node<T>>(node->elem, node->red,
        node->left.ref, node->right.ref, rid);

    //assert(node->left.ref == Node<T>::nil() || node->left.offset >= 0);

    n->left.csn = node->left.csn;
    n->left.offset = node->left.offset;

    n->right.csn = node->right.csn;
    n->right.offset = node->right.offset;

    std::cerr << "copy_node: src " << node << " dst " << n << std::endl;

    return n;
  }

  NodeRef<T> insert_recursive(std::deque<NodeRef<T>>& path,
      T elem, NodeRef<T>& node, uint64_t rid);

  template<typename ChildA, typename ChildB>
  void insert_balance(NodeRef<T>& parent, NodeRef<T>& nn,
      std::deque<NodeRef<T>>& path, ChildA, ChildB, NodeRef<T>& root,
      uint64_t rid);

  template <typename ChildA, typename ChildB >
  NodeRef<T> rotate(NodeRef<T> parent, NodeRef<T> child,
      ChildA child_a, ChildB child_b, NodeRef<T>& root,
      uint64_t rid);

  void print_path(std::deque<NodeRef<T>>& path);
  void print_node(NodeRef<T> node);

  NodeRef<T> root_;

  PTree() {}
  std::vector<std::string> *db_;

  // this is created by the first tree instance made when the db is supplied
  // and then it is passed along after each insert. this is pretty ugly. the
  // node cache needs to be a stand-alone thing.
  std::map<std::pair<uint64_t, int>, NodeRef<T>> *node_cache_;

  void node_cache_get_(NodePtr<T>& ptr) {
    assert(ptr.ref == nullptr);
    std::cerr << "node_cache_get_: csn " << ptr.csn << " off " << ptr.offset << std::endl;
    auto it = node_cache_->find(std::make_pair(ptr.csn, ptr.offset));
    bool cached = it != node_cache_->end();
    if (cached) {
      ptr.ref = it->second;
      return;
    }

    // read and deserialize intention from log
    std::string snapshot = db_->at(ptr.csn);
    kvstore_proto::Intention i;
    assert(i.ParseFromString(snapshot));
    assert(i.IsInitialized());

    const kvstore_proto::Node& n = i.tree(ptr.offset);

    // here we use rid == log offset. itd be nice to have something uniquely
    // generated in memory as a safety net. we can use a csn->rid map to
    // handle this.
    auto nn = std::make_shared<Node<T>>(n.value(), n.red(),
        Node<T>::nil(), Node<T>::nil(), ptr.csn);

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

    node_cache_->insert(std::make_pair(std::make_pair(ptr.csn, ptr.offset), nn));

    ptr.ref = nn;
  }

  static uint64_t root_id_;

  static NodePtr<T>& left(NodeRef<T> n) { return n->left; };
  static NodePtr<T>& right(NodeRef<T> n) { return n->right; };

  static NodeRef<T> pop_front(std::deque<NodeRef<T>>& d) {
    auto front = d.front();
    d.pop_front();
    return front;
  }
};

template<typename T>
PTree<T>::PTree(std::vector<std::string> *db) :
  db_(db), node_cache_(NULL)
{
  // TODO: inistialize an empty db with an append at pos 0 of an empty tree?
  root_ = Node<T>::nil();
  node_cache_ = new std::map<std::pair<uint64_t, int>, NodeRef<T>>();
}

template<typename T>
uint64_t PTree<T>::root_id_ = 928734;

template<typename T>
void PTree<T>::write_dot_null(std::ostream& out,
    NodeRef<T> node, uint64_t& nullcount)
{
  nullcount++;
  out << "null" << nullcount << " [shape=point];"
    << std::endl;
  out << "\"" << node.get() << "\" -> " << "null"
    << nullcount << " [label=\"nil\"];" << std::endl;
}

template<typename T>
void PTree<T>::write_dot_node(std::ostream& out,
    NodeRef<T> parent, NodePtr<T>& child, const std::string& dir)
{
  out << "\"" << parent.get() << "\":" << dir << " -> ";
  out << "\"" << child.ref.get() << "\"";
  out << " [label=\"" << child.csn << ":"
    << child.offset << "\"];" << std::endl;
}

template<typename T>
void PTree<T>::write_dot_recursive(std::ostream& out, uint64_t rid,
    NodeRef<T> node, uint64_t& nullcount, bool scoped)
{
  if (scoped && node->rid != rid)
    return;

  out << "\"" << node.get() << "\" ["
    << "label=" << node->elem << ",style=filled,"
    << "fillcolor=" << (node->red ? "red" :
        "black,fontcolor=white")
    << "]" << std::endl;

  if (node->left.ref == Node<T>::nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->left, "sw");
    write_dot_recursive(out, rid, node->left.ref, nullcount, scoped);
  }

  if (node->right.ref == Node<T>::nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->right, "se");
    write_dot_recursive(out, rid, node->right.ref, nullcount, scoped);
  }
}

template<typename T>
void PTree<T>::_write_dot(std::ostream& out,
    uint64_t& nullcount, bool scoped)
{
  write_dot_recursive(out, root_->rid,
      root_, nullcount, scoped);
}

template<typename T>
void PTree<T>::write_dot(std::ostream& out, bool scoped)
{
  uint64_t nullcount = 0;
  out << "digraph ptree {" << std::endl;
  _write_dot(out, nullcount, scoped);
  out << "}" << std::endl;
}

template<typename T>
void PTree<T>::write_dot(std::ostream& out,
    std::vector<PTree<T>>& versions)
{
  uint64_t trees = 0;
  uint64_t nullcount = 0;
  out << "digraph ptree {" << std::endl;
  for (auto version : versions) {
    out << "subgraph cluster_" << trees++ << " {" << std::endl;
    version._write_dot(out, nullcount, true);
    out << "}" << std::endl;
  }
  out << "}" << std::endl;
}

template<typename T>
NodeRef<T> PTree<T>::insert_recursive(std::deque<NodeRef<T>>& path,
    T elem, NodeRef<T>& node, uint64_t rid)
{
  std::cerr << "insert_recursive(" << elem << "): " << node << " : " << node->elem << std::endl;
  if (node == Node<T>::nil()) {
    // in C++17 replace with `return path.emplace_back(...)`
    auto nn = std::make_shared<Node<T>>(elem, true, Node<T>::nil(), Node<T>::nil(), rid);
    path.push_back(nn);
    std::cerr << "make-node: " << nn << " : " << elem << std::endl;
    return nn;
  }

  bool less = elem < node->elem;
  bool equal = !less && elem == node->elem;

  if (equal)
    return nullptr;

  auto child = insert_recursive(path, elem,
      (less ? node->left.ref : node->right.ref),
      rid);

  if (child == nullptr)
    return child;

  /*
   * the copy_node operation will copy the child node references, as well as
   * the csn/offset for each child node reference. however below the reference
   * is updated without updating the csn/offset, which are fixed later when
   * the intention is build.
   */
  auto copy = copy_node(node, rid);

  if (less)
    copy->left.ref = child;
  else
    copy->right.ref = child;

  path.push_back(copy);

  return copy;
}

template<typename T>
template<typename ChildA, typename ChildB >
NodeRef<T> PTree<T>::rotate(NodeRef<T> parent,
    NodeRef<T> child, ChildA child_a, ChildB child_b, NodeRef<T>& root,
    uint64_t rid)
{
  // copy over ref and csn/off because we might be moving a pointer that
  // points outside of the current intentino.
  NodePtr<T> grand_child = child_b(child);
  child_b(child) = child_a(grand_child.ref);

  if (root == child) {
    root = grand_child.ref;
  } else if (child_a(parent).ref == child)
    child_a(parent) = grand_child;
  else
    child_b(parent) = grand_child;

  // we do not update csn/off here because child is always a pointer to a node
  // in the current intention so its csn/off will be updated during intention
  // serialization step.
  assert(child->rid == rid);
  child_a(grand_child.ref).ref = child;

  return grand_child.ref;
}

template<typename T>
template<typename ChildA, typename ChildB>
void PTree<T>::insert_balance(NodeRef<T>& parent, NodeRef<T>& nn,
    std::deque<NodeRef<T>>& path, ChildA child_a, ChildB child_b,
    NodeRef<T>& root, uint64_t rid)
{
  assert(path.front() != Node<T>::nil());
  NodePtr<T>& uncle = child_b(path.front());
  if (uncle.ref->red) {
    std::cerr << "insert_balance: copy uncle " << uncle.ref << std::endl;
    uncle.ref = copy_node(uncle.ref, rid);
    parent->red = false;
    uncle.ref->red = false;
    path.front()->red = true;
    nn = pop_front(path);
    parent = pop_front(path);
  } else {
    if (nn == child_b(parent).ref) {
      std::swap(nn, parent);
      rotate(path.front(), nn, child_a, child_b, root, rid);
    }
    auto grand_parent = pop_front(path);
    std::swap(grand_parent->red, parent->red);
    rotate(path.front(), grand_parent, child_b, child_a, root, rid);
  }
}

template<typename T>
PTree<T> PTree<T>::insert(T elem)
{
  uint64_t rid = root_id_++;

  std::deque<NodeRef<T>> path;

  auto root = insert_recursive(path, elem, root_, rid);
  if (root == nullptr)
    return *this;

  path.push_back(Node<T>::nil());

  assert(path.size() >= 2);

  auto nn = pop_front(path);
  auto parent = pop_front(path);

  while (parent->red) {
    assert(!path.empty());
    auto grand_parent = path.front();
    if (grand_parent->left.ref == parent)
      insert_balance(parent, nn, path, left, right, root, rid);
    else
      insert_balance(parent, nn, path, right, left, root, rid);
  }

  root->red = false;

  // build an intention for the new tree
  kvstore_proto::Intention intention;
  serialize_intention(intention, root);

  // append to the database log
  std::string blob;
  assert(intention.IsInitialized());
  assert(intention.SerializeToString(&blob));
  db_->push_back(blob);
  uint64_t pos = db_->size() - 1;

  // update the in-memory intention ptrs
  set_intention_self_csn(root, pos);

  std::cerr << intention << std::endl;

  PTree<T> tree;
  tree.root_ = root;
  tree.db_ = db_;
  tree.node_cache_ = node_cache_;
  return tree;
}

template<typename T>
void PTree<T>::print_node(NodeRef<T> node)
{
  if (node == Node<T>::nil())
    std::cout << "nil:" << (node->red ? "r" : "b");
  else
    std::cout << node->elem << ":" << (node->red ? "r" : "b");
}

template<typename T>
void PTree<T>::print_path(std::deque<NodeRef<T>>& path)
{
  std::cout << "path: ";
  if (path.empty()) {
    std::cout << "<empty>";
  } else {
    std::cout << "[";
    for (auto node : path) {
      if (node == Node<T>::nil())
        std::cout << "nil:" << (node->red ? "r " : "b ");
      else
        std::cout << node->elem << ":" << (node->red ? "r " : "b ");
    }
    std::cout << "]";
  }
  std::cout << std::endl;
}

template<typename T>
bool PTree<T>::validate_rb_tree()
{
  return _validate_rb_tree(root_) != 0;
}

template<typename T>
int PTree<T>::_validate_rb_tree(NodeRef<T> root)
{
  if (root == Node<T>::nil())
    return 1;

  NodeRef<T> ln = root->left.ref;
  NodeRef<T> rn = root->right.ref;

  if (root->red && (ln->red || rn->red))
    return 0;

  int lh = _validate_rb_tree(ln);
  int rh = _validate_rb_tree(rn);

  if ((ln != Node<T>::nil() && ln->elem >= root->elem) ||
      (rn != Node<T>::nil() && rn->elem <= root->elem))
    return 0;

  if (lh != 0 && rh != 0 && lh != rh)
    return 0;

  if (lh != 0 && rh != 0)
    return root->red ? lh : lh + 1;

  return 0;
}
#endif
