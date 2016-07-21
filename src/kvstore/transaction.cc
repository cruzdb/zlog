#include "transaction.h"
#include <deque>
#include "db.h"

void Transaction::serialize_node(kvstore_proto::Node *n, NodeRef node,
    uint64_t rid, int field_index) {

  n->set_red(node->red);
  n->set_value(node->elem);

  assert(node->field_index == -1);
  node->field_index = field_index;
  assert(node->field_index >= 0);

  std::cerr << "serialize_node: " << node << std::endl;

  if (node->left.ref == DB::Nil()) {
    n->mutable_left()->set_nil(true);
    n->mutable_left()->set_self(false);
    n->mutable_left()->set_csn(0);
    n->mutable_left()->set_off(0);
    std::cerr << " - serialize_node: left nil" << std::endl;
  } else if (node->left.ref->rid == rid) {
    n->mutable_left()->set_nil(false);
    n->mutable_left()->set_self(true);
    n->mutable_left()->set_csn(0);
    assert(node->left.ref->field_index >= 0);
    n->mutable_left()->set_off(node->left.ref->field_index);
    node->left.offset = node->left.ref->field_index;
    std::cerr << " - serialize_node: left internal csn " <<
      n->mutable_left()->csn() << " off " << n->mutable_left()->off()
      << std::endl;
  } else {
    assert(node->left.ref != nullptr);
    n->mutable_left()->set_nil(false);
    n->mutable_left()->set_self(false);
    n->mutable_left()->set_csn(node->left.csn);
    n->mutable_left()->set_off(node->left.offset);
    std::cerr << " - serialize_node: left external csn " <<
      n->mutable_left()->csn() << " off " << n->mutable_left()->off()
      << std::endl;
  }

  if (node->right.ref == DB::Nil()) {
    n->mutable_right()->set_nil(true);
    n->mutable_right()->set_self(false);
    n->mutable_right()->set_csn(0);
    n->mutable_right()->set_off(0);
    std::cerr << " - serialize_node: right nil" << std::endl;
  } else if (node->right.ref->rid == rid) {
    n->mutable_right()->set_nil(false);
    n->mutable_right()->set_self(true);
    n->mutable_right()->set_csn(0);
    assert(node->right.ref->field_index >= 0);
    n->mutable_right()->set_off(node->right.ref->field_index);
    node->right.offset = node->right.ref->field_index;
    std::cerr << " - serialize_node: right internal csn " <<
      n->mutable_right()->csn() << " off " << n->mutable_right()->off()
      << std::endl;
  } else {
    assert(node->right.ref != nullptr);
    n->mutable_right()->set_nil(false);
    n->mutable_right()->set_self(false);
    n->mutable_right()->set_csn(node->right.csn);
    n->mutable_right()->set_off(node->right.offset);
    std::cerr << " - serialize_node: right external csn " <<
      n->mutable_right()->csn() << " off " << n->mutable_right()->off()
      << std::endl;
  }
}

NodeRef Transaction::insert_recursive(std::deque<NodeRef>& path,
    std::string elem, NodeRef& node, uint64_t rid)
{
  std::cerr << "insert_recursive(" << elem << "): " << node << " : " << node->elem << std::endl;
  if (node == DB::Nil()) {
    // in C++17 replace with `return path.emplace_back(...)`
    auto nn = std::make_shared<Node>(elem, true, DB::Nil(), DB::Nil(), rid);
    path.push_back(nn);
    std::cerr << "make-node: " << nn << " : " << elem << std::endl;
    return nn;
  }

  bool less = elem < node->elem;
  bool equal = !less && elem == node->elem;

  if (equal)
    return nullptr;

  auto child = insert_recursive(path, elem,
      (less ? node->left.ref : node->right.ref),
      rid);

  if (child == nullptr)
    return child;

  /*
   * the copy_node operation will copy the child node references, as well as
   * the csn/offset for each child node reference. however below the reference
   * is updated without updating the csn/offset, which are fixed later when
   * the intention is build.
   */
  auto copy = DB::copy_node(node, rid);

  if (less)
    copy->left.ref = child;
  else
    copy->right.ref = child;

  path.push_back(copy);

  return copy;
}

template<typename ChildA, typename ChildB >
NodeRef Transaction::rotate(NodeRef parent,
    NodeRef child, ChildA child_a, ChildB child_b, NodeRef& root,
    uint64_t rid)
{
  // copy over ref and csn/off because we might be moving a pointer that
  // points outside of the current intentino.
  NodePtr grand_child = child_b(child);
  child_b(child) = child_a(grand_child.ref);

  if (root == child) {
    root = grand_child.ref;
  } else if (child_a(parent).ref == child)
    child_a(parent) = grand_child;
  else
    child_b(parent) = grand_child;

  // we do not update csn/off here because child is always a pointer to a node
  // in the current intention so its csn/off will be updated during intention
  // serialization step.
  assert(child->rid == rid);
  child_a(grand_child.ref).ref = child;

  return grand_child.ref;
}

template<typename ChildA, typename ChildB>
void Transaction::insert_balance(NodeRef& parent, NodeRef& nn,
    std::deque<NodeRef>& path, ChildA child_a, ChildB child_b,
    NodeRef& root, uint64_t rid)
{
  assert(path.front() != DB::Nil());
  NodePtr& uncle = child_b(path.front());
  if (uncle.ref->red) {
    std::cerr << "insert_balance: copy uncle " << uncle.ref << std::endl;
    uncle.ref = DB::copy_node(uncle.ref, rid);
    parent->red = false;
    uncle.ref->red = false;
    path.front()->red = true;
    nn = pop_front(path);
    parent = pop_front(path);
  } else {
    if (nn == child_b(parent).ref) {
      std::swap(nn, parent);
      rotate(path.front(), nn, child_a, child_b, root, rid);
    }
    auto grand_parent = pop_front(path);
    std::swap(grand_parent->red, parent->red);
    rotate(path.front(), grand_parent, child_b, child_a, root, rid);
  }
}

void Transaction::serialize_intention_recursive(kvstore_proto::Intention& i,
    uint64_t rid, NodeRef node, int& field_index) {

  if (node == DB::Nil() || node->rid != rid)
    return;

  serialize_intention_recursive(i, rid, node->left.ref, field_index);
  serialize_intention_recursive(i, rid, node->right.ref, field_index);

  // new serialized node in the intention
  kvstore_proto::Node *n = i.add_tree();
  serialize_node(n, node, rid, field_index);
  field_index++;
}

void Transaction::serialize_intention(kvstore_proto::Intention& i, NodeRef node) {
  int field_index = 0;
  serialize_intention_recursive(i, node->rid, node, field_index);
}

void Transaction::set_intention_self_csn_recursive(uint64_t rid,
    NodeRef node, uint64_t pos) {

  if (node == DB::Nil() || node->rid != rid)
    return;

  if (node->right.ref != DB::Nil() && node->right.ref->rid == rid) {
    node->right.csn = pos;
  }

  if (node->left.ref != DB::Nil() && node->left.ref->rid == rid) {
    node->left.csn = pos;
  }

  set_intention_self_csn_recursive(rid, node->right.ref, pos);
  set_intention_self_csn_recursive(rid, node->left.ref, pos);
}

void Transaction::set_intention_self_csn(NodeRef root, uint64_t pos) {
  set_intention_self_csn_recursive(root->rid, root, pos);
}

void Transaction::Put(std::string val)
{
  /*
   * build copy of path to new node
   */
  std::deque<NodeRef> path;

  auto root = insert_recursive(path, val, root_, rid_);
  if (root == nullptr)
    return;

  path.push_back(DB::Nil());
  assert(path.size() >= 2);

  /*
   * balance the tree
   */
  auto nn = pop_front(path);
  auto parent = pop_front(path);

  while (parent->red) {
    assert(!path.empty());
    auto grand_parent = path.front();
    if (grand_parent->left.ref == parent)
      insert_balance(parent, nn, path, left, right, root, rid_);
    else
      insert_balance(parent, nn, path, right, left, root, rid_);
  }

  root->red = false;

  // may want to keep the original root pointer around ???
  root_ = root;
}

void Transaction::Commit()
{
  // build the intention and fixup field offsets
  serialize_intention(intention_, root_);

  // append to the database log
  std::string blob;
  assert(intention_.IsInitialized());
  assert(intention_.SerializeToString(&blob));
  size_t pos = db_->db_log_append(blob);

  // update the in-memory intention ptrs
  set_intention_self_csn(root_, pos);

  //  this needs to be further separated. here should append to the log and
  //  then wait for the db to roll forward to find out if the txn commits.
  //  rather here we just take a short cut during development and do all of
  //  the work.

  std::cerr << intention_ << std::endl;

  db_->db_roots_append(root_);
}
