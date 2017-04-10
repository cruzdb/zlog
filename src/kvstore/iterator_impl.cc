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
  NodeRef node = snapshot_->root.ref();
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
  NodeRef node = snapshot_->root.ref();
  while (node != Node::Nil()) {
    stack_.push(node);
    node = node->right.ref();
  }

  dir = Reverse;
}

void IteratorImpl::Seek(const Slice& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_->root.ref();
  while (node != Node::Nil()) {
    int cmp = key.compare(Slice(node->key().data(),
          node->key().size()));
    if (cmp == 0) {
      stack_.push(node);
      break;
    } else if (cmp < 0) {
      stack_.push(node);
      node = node->left.ref();
    } else
      node = node->right.ref();
  }

  assert(stack_.empty() ||
      Slice(stack_.top()->key().data(),
        stack_.top()->key().size()).compare(key) >= 0);

  dir = Forward;
}

void IteratorImpl::SeekForward(const Slice& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_->root.ref();
  while (node != Node::Nil()) {
    int cmp = key.compare(Slice(node->key().data(),
          node->key().size()));
    if (cmp == 0) {
      stack_.push(node);
      break;
    } else if (cmp < 0) {
      stack_.push(node);
      node = node->left.ref();
    } else
      node = node->right.ref();
  }

  assert(stack_.empty() ||
      Slice(stack_.top()->key().data(),
        stack_.top()->key().size()).compare(key) == 0);

  dir = Forward;
}

void IteratorImpl::SeekPrevious(const Slice& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_->root.ref();
  while (node != Node::Nil()) {
    int cmp = key.compare(Slice(node->key().data(),
          node->key().size()));
    if (cmp == 0) {
      stack_.push(node);
      break;
    } else if (cmp < 0) {
      node = node->left.ref();
    } else {
      stack_.push(node);
      node = node->right.ref();
    }
  }

  assert(stack_.empty() ||
      Slice(stack_.top()->key().data(),
        stack_.top()->key().size()).compare(key) == 0);

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

Slice IteratorImpl::key() const
{
  assert(Valid());
  return Slice(stack_.top()->key().data(),
      stack_.top()->key().size());
}

Slice IteratorImpl::value() const
{
  assert(Valid());
  return Slice(stack_.top()->val().data(),
      stack_.top()->val().size());
}
