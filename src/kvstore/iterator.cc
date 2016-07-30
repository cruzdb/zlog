#include "iterator.h"

#include "iterator.h"

Iterator::Iterator(Snapshot snapshot) : curr_(Node::Nil()), snapshot_(snapshot)
{
}

bool Iterator::Valid() const
{
  return curr_ != Node::Nil();
}

void Iterator::SeekToFirst()
{
  std::stack<NodeRef> stack;
  NodeRef node = snapshot_.root;
  if (node == Node::Nil()) {
    curr_ = Node::Nil();
    stack_.swap(stack);
    return;
  }
  stack.push(Node::Nil());
  while (node->left.ref() != Node::Nil()) {
    stack.push(node);
    node = node->left.ref();
  }
  stack_.swap(stack);
  curr_ = node;
}

void Iterator::SeekToLast()
{
  std::stack<NodeRef> stack;
  NodeRef node = snapshot_.root;
  if (node == Node::Nil()) {
    curr_ = Node::Nil();
    return;
  }
  stack.push(Node::Nil());
  while (node->right.ref() != Node::Nil()) {
    stack.push(node);
    node = node->right.ref();
  }
  stack_.swap(stack);
  curr_ = node;
}

void Iterator::Next()
{
  assert(Valid());
  NodeRef node = curr_->right.ref();
  if (node != Node::Nil()) {
    while (node->left.ref() != Node::Nil()) {
      stack_.push(node);
      node = node->left.ref();
    }
  } else {
    node = stack_.top();
    stack_.pop();
  }
  curr_ = node;
}

std::string Iterator::key() const
{
  assert(Valid());
  return curr_->key();
}

std::string Iterator::value() const
{
  assert(Valid());
  return curr_->val();
}
