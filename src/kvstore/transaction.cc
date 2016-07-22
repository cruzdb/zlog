#include "transaction.h"
#include <deque>
#include "db.h"

void Transaction::serialize_node_ptr(kvstore_proto::NodePtr *dst,
    NodePtr& src, const std::string& dir) const
{
  if (src.ref == Node::Nil()) {
    dst->set_nil(true);
    dst->set_self(false);
    dst->set_csn(0);
    dst->set_off(0);
    std::cerr << " - serialize_node: " << dir << " nil" << std::endl;
  } else if (src.ref->rid == rid_) {
    dst->set_nil(false);
    dst->set_self(true);
    dst->set_csn(0);
    assert(src.ref->field_index >= 0);
    dst->set_off(src.ref->field_index);
    src.offset = src.ref->field_index;
    std::cerr << " - serialize_node: " << dir << " internal csn " <<
      dst->csn() << " off " << dst->off()
      << std::endl;
  } else {
    assert(src.ref != nullptr);
    dst->set_nil(false);
    dst->set_self(false);
    dst->set_csn(src.csn);
    dst->set_off(src.offset);
    std::cerr << " - serialize_node: " << dir << " external csn " <<
      dst->csn() << " off " << dst->off()
      << std::endl;
  }
}

void Transaction::serialize_node(kvstore_proto::Node *dst,
    NodeRef node, int field_index) const
{
  dst->set_red(node->red);
  dst->set_value(node->elem);

  assert(node->field_index == -1);
  node->field_index = field_index;
  assert(node->field_index >= 0);

  serialize_node_ptr(dst->mutable_left(), node->left, "left");
  serialize_node_ptr(dst->mutable_right(), node->right, "right");
}

NodeRef Transaction::insert_recursive(std::deque<NodeRef>& path,
    std::string elem, NodeRef& node)
{
  std::cerr << "insert_recursive(" << elem << "): " << node << " : " << node->elem << std::endl;
  if (node == Node::Nil()) {
    // in C++17 replace with `return path.emplace_back(...)`
    auto nn = std::make_shared<Node>(elem, true, Node::Nil(), Node::Nil(), rid_);
    path.push_back(nn);
    std::cerr << "make-node: " << nn << " : " << elem << std::endl;
    return nn;
  }

  bool less = elem < node->elem;
  bool equal = !less && elem == node->elem;

  if (equal)
    return nullptr;

  auto child = insert_recursive(path, elem,
      (less ? node->left.ref : node->right.ref));

  if (child == nullptr)
    return child;

  /*
   * the copy_node operation will copy the child node references, as well as
   * the csn/offset for each child node reference. however below the reference
   * is updated without updating the csn/offset, which are fixed later when
   * the intention is build.
   */
  auto copy = Node::Copy(node, rid_);

  if (less)
    copy->left.ref = child;
  else
    copy->right.ref = child;

  path.push_back(copy);

  return copy;
}

template<typename ChildA, typename ChildB >
NodeRef Transaction::rotate(NodeRef parent,
    NodeRef child, ChildA child_a, ChildB child_b, NodeRef& root)
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
  assert(child->rid == rid_);
  child_a(grand_child.ref).ref = child;

  return grand_child.ref;
}

template<typename ChildA, typename ChildB>
void Transaction::insert_balance(NodeRef& parent, NodeRef& nn,
    std::deque<NodeRef>& path, ChildA child_a, ChildB child_b,
    NodeRef& root)
{
  assert(path.front() != Node::Nil());
  NodePtr& uncle = child_b(path.front());
  if (uncle.ref->red) {
    std::cerr << "insert_balance: copy uncle " << uncle.ref << std::endl;
    uncle.ref = Node::Copy(uncle.ref, rid_);
    parent->red = false;
    uncle.ref->red = false;
    path.front()->red = true;
    nn = pop_front(path);
    parent = pop_front(path);
  } else {
    if (nn == child_b(parent).ref) {
      std::swap(nn, parent);
      rotate(path.front(), nn, child_a, child_b, root);
    }
    auto grand_parent = pop_front(path);
    std::swap(grand_parent->red, parent->red);
    rotate(path.front(), grand_parent, child_b, child_a, root);
  }
}

void Transaction::serialize_intention(NodeRef node, int& field_index)
{
  if (node == Node::Nil() || node->rid != rid_)
    return;

  serialize_intention(node->left.ref, field_index);
  serialize_intention(node->right.ref, field_index);

  // new serialized node in the intention
  kvstore_proto::Node *dst = intention_.add_tree();
  serialize_node(dst, node, field_index);
  field_index++;
}

void Transaction::set_intention_self_csn_recursive(uint64_t rid,
    NodeRef node, uint64_t pos) {

  if (node == Node::Nil() || node->rid != rid)
    return;

  if (node->right.ref != Node::Nil() && node->right.ref->rid == rid) {
    node->right.csn = pos;
  }

  if (node->left.ref != Node::Nil() && node->left.ref->rid == rid) {
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

  auto root = insert_recursive(path, val, root_);
  if (root == nullptr)
    return;

  path.push_back(Node::Nil());
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
      insert_balance(parent, nn, path, left, right, root);
    else
      insert_balance(parent, nn, path, right, left, root);
  }

  root->red = false;

  // may want to keep the original root pointer around ???
  root_ = root;
}

void Transaction::Commit()
{
  // build the intention and fixup field offsets
  int field_index = 0;
  assert(root_->rid == rid_);
  serialize_intention(root_, field_index);

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
  //
  //  first simplification to work torwards this goal is to model meld, but
  //  only handle the serial case which makes its implementation trivial.

  std::cerr << intention_ << std::endl;

  db_->db_roots_append(root_);
}
