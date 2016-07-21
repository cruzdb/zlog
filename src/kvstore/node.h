#ifndef ZLOG_KVSTORE_NODE_H
#define ZLOG_KVSTORE_NODE_H
#include <memory>
#include <string>

struct Node;
using NodeRef = std::shared_ptr<Node>;

/*
 *
 */
struct NodePtr {
  NodeRef ref;
  int64_t csn;
  int offset;

  NodePtr() : NodePtr(nullptr) {}

  explicit NodePtr(NodeRef ref) :
    ref(ref), csn(-1), offset(-1)
  {}
};

/*
 *
 */
struct Node {
  std::string elem;
  bool red;
  NodePtr left;
  NodePtr right;

  uint64_t rid;
  int field_index;

  Node(std::string elem, bool red, NodeRef lr, NodeRef rr, uint64_t rid) :
    elem(elem), red(red), left(lr), right(rr), rid(rid), field_index(-1)
  {}
};

#endif
