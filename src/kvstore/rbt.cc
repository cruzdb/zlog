#include <cassert>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <memory>
#include <set>
#include <stack>
#include <vector>

template<typename T>
class PTree {
 public:
  PTree();

  PTree<T> insert(T elem);

  std::set<T> stl_set() {
    std::set<T> set;
    NodePtr node = root_;
    if (node == nil())
      return set;
    std::stack<NodePtr> stack;
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
  using NodePtr = std::shared_ptr<Node>;

  struct Node {
    T elem;
    bool red;
    NodePtr left;
    NodePtr right;

    Node(T elem, bool red, NodePtr left, NodePtr right) :
      elem(elem), red(red), left(left), right(right)
    {}
  };

  NodePtr copy_node(NodePtr node) const {
    if (node == nil())
      return nil();
    return std::make_shared<Node>(node->elem, node->red,
        node->left, node->right);
  }

  NodePtr insert_recursive(std::deque<NodePtr>& path,
      T elem, NodePtr node);

  template<typename ChildA, typename ChildB>
  void insert_balance(NodePtr& parent, NodePtr& nn,
      std::deque<NodePtr>& path, ChildA, ChildB, NodePtr& root);

  template <typename ChildA, typename ChildB >
  NodePtr rotate(NodePtr parent, NodePtr child,
      ChildA child_a, ChildB child_b, NodePtr& root);

  void print_path(std::deque<NodePtr>& path);
  void print_node(NodePtr node);

  static NodePtr nil() {
    static NodePtr node = std::make_shared<Node>(T(), false, nullptr, nullptr);
    return node;
  }

  NodePtr root_;

  static NodePtr& left(NodePtr n) { return n->left; };
  static NodePtr& right(NodePtr n) { return n->right; };

  static NodePtr pop_front(std::deque<NodePtr>& d) {
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
typename PTree<T>::NodePtr PTree<T>::insert_recursive(std::deque<NodePtr>& path,
    T elem, NodePtr node)
{
  if (node == nil()) {
    // in C++17 replace with `return path.emplace_back(...)`
    auto nn = std::make_shared<Node>(elem, true, nil(), nil());
    path.push_back(nn);
    return nn;
  }

  bool less = elem < node->elem;
  bool equal = !less && elem == node->elem;

  if (equal)
    return nullptr;

  auto child = insert_recursive(path, elem,
      (less ? node->left : node->right));

  if (child == nullptr)
    return child;

  auto copy = copy_node(node);

  if (less)
    copy->left = child;
  else
    copy->right = child;

  path.push_back(copy);

  return copy;
}

template<typename T>
template<typename ChildA, typename ChildB >
typename PTree<T>::NodePtr PTree<T>::rotate(NodePtr parent,
    NodePtr child, ChildA child_a, ChildB child_b, NodePtr& root)
{
  NodePtr grand_child = child_b(child);
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
void PTree<T>::insert_balance(NodePtr& parent, NodePtr& nn,
    std::deque<NodePtr>& path, ChildA child_a, ChildB child_b,
    NodePtr& root)
{
  assert(path.front() != nil());
  NodePtr& uncle = child_b(path.front());
  if (uncle->red) {
    uncle = copy_node(uncle);
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
  std::deque<NodePtr> path;

  auto root = insert_recursive(path, elem, root_);
  if (root == nullptr)
    return *this;

  path.push_back(nil());

  std::cout << "new-root: ";
  print_node(root);
  std::cout << std::endl;
  print_path(path);

  assert(path.size() >= 2);

  auto nn = pop_front(path);
  NodePtr parent = pop_front(path);

  while (parent->red) {
    assert(!path.empty());
    auto grand_parent = path.front();
    if (grand_parent->left == parent)
      insert_balance(parent, nn, path, left, right, root);
    else
      insert_balance(parent, nn, path, right, left, root);
  }

  root->red = false;

  PTree<T> tree;
  tree.root_ = root;
  return tree;
}

template<typename T>
void PTree<T>::print_node(NodePtr node)
{
  if (node == nil())
    std::cout << "nil:" << (node->red ? "r" : "b");
  else
    std::cout << node->elem << ":" << (node->red ? "r" : "b");
}

template<typename T>
void PTree<T>::print_path(std::deque<NodePtr>& path)
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

int main(int argc, char **argv)
{
  while (1) {
    std::vector<std::set<int>> truth_history;
    std::set<int> truth;
    truth_history.push_back(truth);

    std::vector<PTree<int>> tree_history;
    PTree<int> tree;
    tree_history.push_back(tree);

    for (int i = 0; i < 1000; i++) {
      int val = std::rand();

      truth.insert(val);
      truth_history.push_back(truth);

      tree = tree.insert(val);
      tree_history.push_back(tree);
    }

    assert(truth_history.size() == tree_history.size());
    for (unsigned i = 0; i < truth_history.size(); i++)
      assert(truth_history[i] == tree_history[i].stl_set());
  }

  return 0;
}
