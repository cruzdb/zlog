#ifndef ZLOG_KVSTORE_PTREE_H
#define ZLOG_KVSTORE_PTREE_H
#include <cassert>
#include <deque>
#include <set>
#include <iostream>
#include <memory>
#include <stack>
#include <vector>

template<typename T>
class PTree {
 public:
  PTree();

  PTree<T> insert(T elem);

  std::set<T> stl_set() {
    std::set<T> set;
    NodeRef node = root_;
    if (node == nil())
      return set;
    std::stack<NodeRef> stack;
    stack.push(node);
    while (!stack.empty()) {
      node = stack.top();
      stack.pop();
      auto ret = set.emplace(node->elem);
      assert(ret.second);
      if (node->right != nil())
        stack.push(node->right);
      if (node->left != nil())
        stack.push(node->left);
    }
    return set;
  }

 private:
  struct Node;
  using NodeRef = std::shared_ptr<Node>;

  struct Node {
    T elem;
    bool red;
    NodeRef left;
    NodeRef right;
    uint64_t rid;

    Node(T elem, bool red, NodeRef left, NodeRef right,
        uint64_t rid) :
      elem(elem), red(red), left(left), right(right), rid(rid)
    {}
  };

  void write_dot_recursive(std::ostream& out, uint64_t rid,
      NodeRef node, uint64_t& nullcount, bool scoped);
  void write_dot_null(std::ostream& out, NodeRef node, uint64_t& nullcount);
  void write_dot_node(std::ostream& out, NodeRef parent,
      NodeRef child, const std::string& dir);
  void _write_dot(std::ostream& out, uint64_t& nullcount, bool scoped = false);

  int _validate_rb_tree(NodeRef root);

 public:
  bool validate_rb_tree();
  void write_dot(std::ostream& out, bool scoped = false);
  void write_dot(std::ostream& out,
      std::vector<PTree<T>>& versions);

 private:
  NodeRef copy_node(NodeRef node, uint64_t rid) const {
    if (node == nil())
      return nil();
    auto n = std::make_shared<Node>(node->elem, node->red,
        node->left, node->right, rid);
    std::cerr << "copy-node: " << n << " : " << node->elem << std::endl;
    return n;
  }

  NodeRef insert_recursive(std::deque<NodeRef>& path,
      T elem, NodeRef& node, uint64_t rid);

  template<typename ChildA, typename ChildB>
  void insert_balance(NodeRef& parent, NodeRef& nn,
      std::deque<NodeRef>& path, ChildA, ChildB, NodeRef& root,
      uint64_t rid);

  template <typename ChildA, typename ChildB >
  NodeRef rotate(NodeRef parent, NodeRef child,
      ChildA child_a, ChildB child_b, NodeRef& root);

  void print_path(std::deque<NodeRef>& path);
  void print_node(NodeRef node);

  static NodeRef nil() {
    static NodeRef node = std::make_shared<Node>(T(), false, nullptr, nullptr, 0);
    return node;
  }

  NodeRef root_;

  static uint64_t root_id_;

  static NodeRef& left(NodeRef n) { return n->left; };
  static NodeRef& right(NodeRef n) { return n->right; };

  static NodeRef pop_front(std::deque<NodeRef>& d) {
    auto front = d.front();
    d.pop_front();
    return front;
  }
};

template<typename T>
PTree<T>::PTree()
{
  root_ = nil();
}

template<typename T>
uint64_t PTree<T>::root_id_ = 1;

template<typename T>
void PTree<T>::write_dot_null(std::ostream& out,
    NodeRef node, uint64_t& nullcount)
{
  nullcount++;
  out << "null" << nullcount << " [shape=point];"
    << std::endl;
  out << "\"" << node << "\" -> " << "null"
    << nullcount << ";" << std::endl;
}

template<typename T>
void PTree<T>::write_dot_node(std::ostream& out,
    NodeRef parent, NodeRef child, const std::string& dir)
{
  out << "\"" << parent << "\":" << dir << " -> ";
  out << "\"" << child << "\"" << std::endl;
}

template<typename T>
void PTree<T>::write_dot_recursive(std::ostream& out, uint64_t rid,
    NodeRef node, uint64_t& nullcount, bool scoped)
{
  if (scoped && node->rid != rid)
    return;

  out << "\"" << node << "\" ["
    << "label=" << node->elem << ",style=filled,"
    << "fillcolor=" << (node->red ? "red" :
        "black,fontcolor=white")
    << "]" << std::endl;

  if (node->left == nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->left, "sw");
    write_dot_recursive(out, rid, node->left, nullcount, scoped);
  }

  if (node->right == nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->right, "se");
    write_dot_recursive(out, rid, node->right, nullcount, scoped);
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
typename PTree<T>::NodeRef PTree<T>::insert_recursive(std::deque<NodeRef>& path,
    T elem, NodeRef& node, uint64_t rid)
{
  std::cerr << "insert_recursive(" << elem << "): " << node << " : " << node->elem << std::endl;
  if (node == nil()) {
    // in C++17 replace with `return path.emplace_back(...)`
    auto nn = std::make_shared<Node>(elem, true, nil(), nil(), rid);
    path.push_back(nn);
    std::cerr << "make-node: " << nn << " : " << elem << std::endl;
    return nn;
  }

  bool less = elem < node->elem;
  bool equal = !less && elem == node->elem;

  if (equal)
    return nullptr;

  auto child = insert_recursive(path, elem,
      (less ? node->left : node->right),
      rid);

  if (child == nullptr)
    return child;

  auto copy = copy_node(node, rid);

  if (less)
    copy->left = child;
  else
    copy->right = child;

  path.push_back(copy);

  return copy;
}

template<typename T>
template<typename ChildA, typename ChildB >
typename PTree<T>::NodeRef PTree<T>::rotate(NodeRef parent,
    NodeRef child, ChildA child_a, ChildB child_b, NodeRef& root)
{
  NodeRef grand_child = child_b(child);
  child_b(child) = child_a(grand_child);

  if (root == child) {
    root = grand_child;
  } else if (child_a(parent) == child)
    child_a(parent) = grand_child;
  else
    child_b(parent) = grand_child;

  child_a(grand_child) = child;

  return grand_child;
}

template<typename T>
template<typename ChildA, typename ChildB>
void PTree<T>::insert_balance(NodeRef& parent, NodeRef& nn,
    std::deque<NodeRef>& path, ChildA child_a, ChildB child_b,
    NodeRef& root, uint64_t rid)
{
  assert(path.front() != nil());
  NodeRef& uncle = child_b(path.front());
  if (uncle->red) {
    std::cerr << "unclde red" << std::endl;
    uncle = copy_node(uncle, rid);
    parent->red = false;
    uncle->red = false;
    path.front()->red = true;
    nn = pop_front(path);
    parent = pop_front(path);
  } else {
    if (nn == child_b(parent)) {
      std::swap(nn, parent);
      rotate(path.front(), nn, child_a, child_b, root);
    }
    auto grand_parent = pop_front(path);
    std::swap(grand_parent->red, parent->red);
    rotate(path.front(), grand_parent, child_b, child_a, root);
  }
}

template<typename T>
PTree<T> PTree<T>::insert(T elem)
{
  uint64_t rid = root_id_++;

  std::deque<NodeRef> path;

  auto root = insert_recursive(path, elem, root_, rid);
  if (root == nullptr)
    return *this;

  path.push_back(nil());

  assert(path.size() >= 2);

  auto nn = pop_front(path);
  auto parent = pop_front(path);

  while (parent->red) {
    assert(!path.empty());
    auto grand_parent = path.front();
    if (grand_parent->left == parent)
      insert_balance(parent, nn, path, left, right, root, rid);
    else
      insert_balance(parent, nn, path, right, left, root, rid);
  }

  root->red = false;

  PTree<T> tree;
  tree.root_ = root;
  return tree;
}

template<typename T>
void PTree<T>::print_node(NodeRef node)
{
  if (node == nil())
    std::cout << "nil:" << (node->red ? "r" : "b");
  else
    std::cout << node->elem << ":" << (node->red ? "r" : "b");
}

template<typename T>
void PTree<T>::print_path(std::deque<NodeRef>& path)
{
  std::cout << "path: ";
  if (path.empty()) {
    std::cout << "<empty>";
  } else {
    std::cout << "[";
    for (auto node : path) {
      if (node == nil())
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
int PTree<T>::_validate_rb_tree(PTree<T>::NodeRef root)
{
  if (root == nil())
    return 1;

  NodeRef ln = root->left;
  NodeRef rn = root->right;

  if (root->red && (ln->red || rn->red))
    return 0;

  int lh = _validate_rb_tree(ln);
  int rh = _validate_rb_tree(rn);

  if ((ln != nil() && ln->elem >= root->elem) ||
      (rn != nil() && rn->elem <= root->elem))
    return 0;

  if (lh != 0 && rh != 0 && lh != rh)
    return 0;

  if (lh != 0 && rh != 0)
    return root->red ? lh : lh + 1;

  return 0;
}
#endif
