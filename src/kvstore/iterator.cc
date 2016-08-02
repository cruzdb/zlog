#include "iterator.h"

Iterator::Iterator(Snapshot snapshot) :
  snapshot_(snapshot)
{
}

bool Iterator::Valid() const
{
  return !stack_.empty();
}

void Iterator::SeekToFirst()
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  // all the way to the left
  NodeRef node = snapshot_.root;
  while (node != Node::Nil()) {
    stack_.push(node);
    node = node->left.ref();
  }

  dir = 1; // forward
}

void Iterator::SeekToLast()
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  // all the way to the right
  NodeRef node = snapshot_.root;
  while (node != Node::Nil()) {
    stack_.push(node);
    node = node->right.ref();
  }

  dir = 0; // backward
}

void Iterator::Seek(const std::string& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_.root;
  while (node != Node::Nil()) {
    if (key == node->key()) {
      stack_.push(node);
      break;
    } else if (key < node->key()) {
      NodeRef parent = node;
      node = node->left.ref();
      if (node != Node::Nil() && node->key() < key) {
        stack_.push(parent);
        break;
      }
      stack_.push(parent);
    } else
      node = node->right.ref();
  }

  if (!stack_.empty() && stack_.top()->key() < key) {
    // not found: clear stack
    std::stack<NodeRef> stack;
    stack_.swap(stack);
  }

  dir = 1; // forward
}

void Iterator::SeekForward(const std::string& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_.root;
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

  dir = 1; // forward
}

void Iterator::SeekPrevious(const std::string& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_.root;
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

  dir = 0; // backward
}

void Iterator::Next()
{
  assert(Valid());
  if (dir == 0) {
    SeekForward(key());
    dir = 1;
  }
  assert(Valid());
  NodeRef node = stack_.top()->right.ref();
  stack_.pop();
  while (node != Node::Nil()) {
    stack_.push(node);
    node = node->left.ref();
  }
}

void Iterator::Prev()
{
  assert(Valid());
  if (dir == 1) {
    SeekPrevious(key());
    dir = 0;
  }
  assert(Valid());
  NodeRef node = stack_.top()->left.ref();
  stack_.pop();
  while (node != Node::Nil()) {
    stack_.push(node);
    node = node->right.ref();
  }
}

std::string Iterator::key() const
{
  assert(Valid());
  return stack_.top()->key();
}

std::string Iterator::value() const
{
  assert(Valid());
  return stack_.top()->val();
}
