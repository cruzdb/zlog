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

  bool insert(T elem);

  std::set<T> stl_set() {
    std::set<T> set;
    NodePtr node = roots_.back();
    if (node == nil_)
      return set;
    std::stack<NodePtr> stack;
    stack.push(node);
    while (!stack.empty()) {
      node = stack.top();
      stack.pop();
      auto ret = set.emplace(node->elem);
      assert(ret.second);
      if (node->right != nil_)
        stack.push(node->right);
      if (node->left != nil_)
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
    if (node == nil_)
      return nil_;
    return std::make_shared<Node>(node->elem, node->red,
        node->left, node->right);
  }

  NodePtr insert_recursive(std::deque<NodePtr>& path,
      T elem, NodePtr node);

  template<typename ChildA, typename ChildB>
  void insert_balance(NodePtr& parent, NodePtr& nn,
      std::deque<NodePtr>& path, ChildA, ChildB);

  template <typename ChildA, typename ChildB >
  NodePtr rotate(NodePtr parent, NodePtr child,
      ChildA child_a, ChildB child_b);

  void print_path(std::deque<NodePtr>& path);
  void print_node(NodePtr node);

  const NodePtr nil_;
  std::deque<NodePtr> roots_;

  static NodePtr& left(NodePtr n) { return n->left; };
  static NodePtr& right(NodePtr n) { return n->right; };

  static NodePtr pop_front(std::deque<NodePtr>& d) {
    auto front = d.front();
    d.pop_front();
    return front;
  }
};

template<typename T>
PTree<T>::PTree() :
  nil_(std::make_shared<Node>(T(), false, nullptr, nullptr))
{
  roots_.push_back(nil_);
}

template<typename T>
typename PTree<T>::NodePtr PTree<T>::insert_recursive(std::deque<NodePtr>& path,
    T elem, NodePtr node)
{
  if (node == nil_) {
    // in C++17 replace with `return path.emplace_back(...)`
    auto nn = std::make_shared<Node>(elem, true, nil_, nil_);
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
    NodePtr child, ChildA child_a, ChildB child_b)
{
  NodePtr grand_child = child_b(child);
  child_b(child) = child_a(grand_child);

  if (roots_.back() == child) {
    roots_.pop_back();
    roots_.push_back(grand_child);
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
    std::deque<NodePtr>& path, ChildA child_a, ChildB child_b)
{
  assert(path.front() != nil_);
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
      rotate(path.front(), nn, child_a, child_b);
    }
    auto grand_parent = pop_front(path);
    std::swap(grand_parent->red, parent->red);
    rotate(path.front(), grand_parent, child_b, child_a);
  }
}

template<typename T>
bool PTree<T>::insert(T elem)
{
  std::deque<NodePtr> path;

  auto root = insert_recursive(path, elem, roots_.back());
  if (root == nullptr)
    return false;

  roots_.push_back(root);
  path.push_back(nil_);

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
      insert_balance(parent, nn, path, left, right);
    else
      insert_balance(parent, nn, path, right, left);
  }

  roots_.back()->red = false;

  return true;
}

template<typename T>
void PTree<T>::print_node(NodePtr node)
{
  if (node == nil_)
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
      if (node == nil_)
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
    PTree<int> tree;
    std::set<int> truth;
    std::srand(0);
    for (int i = 0; i < 1000; i++) {
      int val = std::rand();
      truth.insert(val);
      tree.insert(val);
    }
    assert(truth == tree.stl_set());
  }
}
