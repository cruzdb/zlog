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
    // set first
    NodeRef node = snapshot_.root;
    while (node->left.ref() != Node::Nil())
      node = node->left.ref();
    first_ = node;

    // set last
    node = snapshot_.root;
    while (node->right.ref() != Node::Nil())
      node = node->right.ref();
    last_ = node;
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
}

void Iterator::Next()
{
  assert(Valid());
  if (stack_.top() == last_) {
    std::stack<NodeRef> stack;
    stack_.swap(stack);
    assert(!Valid());
    return;
  }
  NodeRef node = stack_.top()->right.ref();
  if (node != Node::Nil()) {
    while (node != Node::Nil()) {
      stack_.push(node);
      node = node->left.ref();
    }
  } else
    stack_.pop();
}

void Iterator::Prev()
{
  assert(Valid());
  if (stack_.top() == first_) {
    std::stack<NodeRef> stack;
    stack_.swap(stack);
    assert(!Valid());
    return;
  }
  NodeRef node = stack_.top()->left.ref();
  if (node != Node::Nil()) {
    while (node != Node::Nil()) {
      stack_.push(node);
      node = node->right.ref();
    }
  } else
    stack_.pop();
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
