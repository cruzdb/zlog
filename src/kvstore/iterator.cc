#include "iterator.h"

/*
 * This iterator implementation can likely be made more efficient. The most
 * annoying part of it is track explicilty the first and last elements in the
 * tree to handle the iteration next/prev edge cases.
 */
Iterator::Iterator(Snapshot snapshot) :
  snapshot_(snapshot)
{
  if (snapshot_.root != Node::Nil()) {
    NodeRef node = snapshot_.root;
    while (node != Node::Nil()) {
      last_ = node;
      node = node->right.ref();
    }
  }
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

  dir = 1; // forward
}

void Iterator::Seek(const std::string& key)
{
  // clear stack
  std::stack<NodeRef> stack;
  stack_.swap(stack);

  NodeRef node = snapshot_.root;
  while (node != Node::Nil()) {
    stack_.push(node);
    if (key == node->key())
      break;
    else if (key < node->key()) {
      node = node->left.ref();
      if (node != Node::Nil() && node->key() < key)
        break;
    } else
      node = node->right.ref();
  }
  if (stack_.top()->key() < key) {
    // not found: clear stack
    std::stack<NodeRef> stack;
    stack_.swap(stack);
  }

  dir = 1; // forward
}

void Iterator::Next()
{
  assert(Valid());
  if (stack_.top() == last_) {
    std::stack<NodeRef> stack;
    stack_.swap(stack);
    return;
  }
  if (dir == 0) {
    Seek(key());
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
    Seek(key());
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
