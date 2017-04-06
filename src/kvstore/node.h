#ifndef ZLOG_KVSTORE_NODE_H
#define ZLOG_KVSTORE_NODE_H
#include <cassert>
#include <memory>
#include <string>
#include <iostream>
#include <vector>

class Node;
using NodeRef = std::shared_ptr<Node>;
using WeakNodeRef = std::weak_ptr<Node>;

class DBImpl;

/*
 * The read-only flag is a temporary hack for enforcing read-only property on
 * the connected Node. What is really needed is a more sophisticated approach
 * that avoids duplicating the read-only flag as well as what is probably some
 * call overhead associated with this design. Overall, this isn't pretty but
 * lets us have confidence in the correctness which is the priority right now.
 * There is probably a lot of overhead always returning copies of the
 * shared_ptr NodeRef.
 *
 * The NodePtr can point to Nil, which is represented by a NodeRef singleton.
 * In this case ref() will resolve to the singleton heap address. Never let
 * the Nil object be freed!
 *
 * In order to handle I/O errors gracefully, including timeouts, etc... we
 * probably will want to allow NodePtr::ref return an error when resolving
 * pointers from storage.
 *
 * Copy assertion should check if we are copying a null pointer that the
 * physical address is defined.
 */
class NodePtr {
 public:

  NodePtr(const NodePtr& other) {
    ref_ = other.ref_;
    offset_ = other.offset_;
    csn_ = other.csn_;
    read_only_ = true;
    db_ = other.db_;
  }

  NodePtr& operator=(const NodePtr& other) {
    assert(!read_only());
    ref_ = other.ref_;
    offset_ = other.offset_;
    csn_ = other.csn_;
    db_ = other.db_;
    return *this;
  }

  // TODO: now we can copy nodeptr. implications?
  //NodePtr(NodePtr&& other) = delete;
  NodePtr& operator=(NodePtr&& other) & = delete;

  NodePtr(NodeRef ref, DBImpl *db, bool read_only) :
    ref_(ref), csn_(-1), offset_(-1), db_(db), read_only_(read_only)
  {}

  void replace(const NodePtr& other) {
    ref_ = other.ref_;
    offset_ = other.offset_;
    csn_ = other.csn_;
    read_only_ = true;
    db_ = other.db_;
  }

  inline bool read_only() const {
    return read_only_;
  }

  inline void set_read_only() {
    assert(!read_only());
    read_only_ = true;
  }

  inline NodeRef ref() {
    while (true) {
      if (auto ret = ref_.lock()) {
        return ret;
      } else {
        ref_ = fetch();
      }
    }
  }

  // this should probably just be handled by the caller... but for the time
  // being it makes the transaction code must simpler.
  inline NodeRef ref(std::vector<std::pair<int64_t, int>>& trace) {
    trace.emplace_back(csn_, offset_);
    return ref();
  }

  inline void set_ref(NodeRef ref) {
    assert(!read_only());
    ref_ = ref;
  }

  inline int offset() const {
    return offset_;
  }

  inline void set_offset(int offset) {
    assert(!read_only());
    offset_ = offset;
  }

  inline int64_t csn() const {
    return csn_;
  }

  inline void set_csn(int64_t csn) {
    assert(!read_only());
    csn_ = csn;
  }

 private:
  // heap pointer (optional), and log address
  WeakNodeRef ref_;
  int64_t csn_;
  int offset_;

  DBImpl *db_;

  bool read_only_;

  NodeRef fetch();
};

/*
 * use signed types here and in protobuf so we can see the initial neg values
 */
class Node {
 public:
  NodePtr left;
  NodePtr right;

  // TODO: allow rid to have negative initialization value
  Node(std::string key, std::string val, bool red, NodeRef lr, NodeRef rr,
      uint64_t rid, int field_index, bool read_only, DBImpl *db) :
    left(lr, db, read_only), right(rr, db, read_only), key_(key), val_(val),
    red_(red), rid_(rid), field_index_(field_index), read_only_(read_only)
  {}

  static NodeRef& Nil() {
    static NodeRef node = std::make_shared<Node>("", "",
        false, nullptr, nullptr, (uint64_t)-1, -1, true, nullptr);
    return node;
  }

  static NodeRef Copy(NodeRef src, DBImpl *db, uint64_t rid) {
    if (src == Nil())
      return Nil();

    auto node = std::make_shared<Node>(src->key(), src->val(), src->red(),
        src->left.ref(), src->right.ref(), rid, -1, false, db);

    node->left.set_csn(src->left.csn());
    node->left.set_offset(src->left.offset());

    node->right.set_csn(src->right.csn());
    node->right.set_offset(src->right.offset());

    return node;
  }

  inline bool read_only() const {
    return read_only_;
  }

  inline void set_read_only() {
    assert(!read_only());
    left.set_read_only();
    right.set_read_only();
    read_only_ = true;
  }

  inline bool red() const {
    return red_;
  }

  inline void set_red(bool red) {
    assert(!read_only());
    red_ = red;
  }

  inline void swap_color(NodeRef other) {
    assert(!read_only());
    assert(!other->read_only());
    std::swap(red_, other->red_);
  }

  inline int field_index() const {
    return field_index_;
  }

  inline void set_field_index(int field_index) {
    assert(!read_only());
    field_index_ = field_index;
  }

  inline uint64_t rid() const {
    return rid_;
  }

  // TODO: return const reference?
  inline std::string key() const {
    return key_;
  }

  // TODO: return const reference?
  inline std::string val() const {
    return val_;
  }

  inline void steal_payload(NodeRef& other) {
    assert(!read_only());
    assert(!other->read_only());
    key_ = std::move(other->key_);
    val_ = std::move(other->val_);
  }

 private:
  std::string key_;
  std::string val_;
  bool red_;
  uint64_t rid_;
  int field_index_;
  bool read_only_;
};

#endif
