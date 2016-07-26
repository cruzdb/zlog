#ifndef ZLOG_KVSTORE_NODE_H
#define ZLOG_KVSTORE_NODE_H
#include <memory>
#include <string>
#include <iostream>

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
 * use signed types here and in protobuf so we can see the initial neg values
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

  static NodeRef& Nil() {
    static NodeRef node = std::make_shared<Node>(
        "", false, nullptr, nullptr, 0);
    return node;
  }

  static NodeRef Copy(NodeRef src, uint64_t rid) {
    if (src == Nil())
      return Nil();

    auto node = std::make_shared<Node>(src->elem, src->red,
        src->left.ref, src->right.ref, rid);

    node->left.csn = src->left.csn;
    node->left.offset = src->left.offset;

    node->right.csn = src->right.csn;
    node->right.offset = src->right.offset;

#if 0
    std::cerr << "copy_node: src " << src << " dst " << node << std::endl;
#endif

    return node;
  }
};

#endif
