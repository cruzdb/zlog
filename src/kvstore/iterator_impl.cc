#include "iterator_impl.h"

IteratorImpl::IteratorImpl(Snapshot *snapshot) :
  snapshot_(snapshot)
{
}

bool IteratorImpl::Valid() const
{
  return !stack_.empty();
}

void IteratorImpl::SeekToFirst()
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  // all the way to the left
  NodeRef node = snapshot_->root;
  while (node != Node::Nil()) {
    stack_.push(node);
    node = node->left.ref();
  }

  dir = Forward;
}

void IteratorImpl::SeekToLast()
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  // all the way to the right
  NodeRef node = snapshot_->root;
  while (node != Node::Nil()) {
    stack_.push(node);
    node = node->right.ref();
  }

  dir = Reverse;
}

void IteratorImpl::Seek(const std::string& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_->root;
  while (node != Node::Nil()) {
    if (key == node->key()) {
      stack_.push(node);
      break;
    } else if (key < node->key()) {
      stack_.push(node);
      node = node->left.ref();
    } else
      node = node->right.ref();
  }

  assert(stack_.empty() || stack_.top()->key() >= key);

  dir = Forward;
}

void IteratorImpl::SeekForward(const std::string& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_->root;
  while (node != Node::Nil()) {
    if (key == node->key()) {
      stack_.push(node);
      break;
    } else if (key < node->key()) {
      stack_.push(node);
      node = node->left.ref();
    } else
      node = node->right.ref();
  }

  assert(stack_.empty() || stack_.top()->key() == key);

  dir = Forward;
}

void IteratorImpl::SeekPrevious(const std::string& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_->root;
  while (node != Node::Nil()) {
    if (key == node->key()) {
      stack_.push(node);
      break;
    } else if (key < node->key()) {
      node = node->left.ref();
    } else {
      stack_.push(node);
      node = node->right.ref();
    }
  }

  assert(stack_.empty() || stack_.top()->key() == key);

  dir = Reverse;
}

void IteratorImpl::Next()
{
  assert(Valid());
  if (dir == Reverse) {
    SeekForward(key());
    assert(dir == Forward);
  }
  assert(Valid());
  NodeRef node = stack_.top()->right.ref();
  stack_.pop();
  while (node != Node::Nil()) {
    stack_.push(node);
    node = node->left.ref();
  }
}

void IteratorImpl::Prev()
{
  assert(Valid());
  if (dir == Forward) {
    SeekPrevious(key());
    assert(dir == Reverse);
  }
  assert(Valid());
  NodeRef node = stack_.top()->left.ref();
  stack_.pop();
  while (node != Node::Nil()) {
    stack_.push(node);
    node = node->right.ref();
  }
}

std::string IteratorImpl::key() const
{
  assert(Valid());
  return stack_.top()->key();
}

std::string IteratorImpl::value() const
{
  assert(Valid());
  return stack_.top()->val();
}
