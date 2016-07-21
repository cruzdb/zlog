#include "db.h"

DB::DB()
{
  roots_.push_back(DB::Nil());

  std::string blob;
  kvstore_proto::Intention intention;
  assert(intention.IsInitialized());
  assert(intention.SerializeToString(&blob));
  db_.push_back(blob);

  // todo: enable/disable debug
  validate_rb_tree();
}

std::set<std::string> DB::stl_set(size_t root) {
  std::set<std::string> set;
  NodeRef node = roots_.at(root);
  if (node == DB::Nil())
    return set;
  std::stack<NodeRef> stack;
  stack.push(node);
  while (!stack.empty()) {
    node = stack.top();
    stack.pop();
    auto ret = set.emplace(node->elem);
    assert(ret.second);
    if (node->right.ref != DB::Nil()) {
      if (node->right.ref == nullptr)
        node_cache_get_(node->right);
      stack.push(node->right.ref);
    }
    if (node->left.ref != DB::Nil()) {
      if (node->left.ref == nullptr)
        node_cache_get_(node->left);
      stack.push(node->left.ref);
    }
  }
  return set;
}

std::set<std::string> DB::stl_set() {
  return stl_set(roots_.size() - 1);
}

std::ostream& operator<<(std::ostream& out, const NodeRef& n)
{
  out << "node(" << n.get() << "):" << n->elem << ": ";
  out << (n->red ? "red " : "blk ");
  out << "fi " << n->field_index << " ";
  out << "left=[p" << n->left.csn << ",o" << n->left.offset << ",";
  out << n->left.ref.get() << "] ";
  out << "right=[p" << n->right.csn << ",o" << n->right.offset << ",";
  out << n->right.ref.get() << "] ";
  return out;
}

std::ostream& operator<<(std::ostream& out, const kvstore_proto::NodePtr& p)
{
  out << "[n" << p.nil() << ",s" << p.self()
    << ",p" << p.csn() << ",o" << p.off() << "]";
  return out;
}

std::ostream& operator<<(std::ostream& out, const kvstore_proto::Node& n)
{
  out << "val " << n.value() << " ";
  out << (n.red() ? "red" : "blk") << " ";
  out << "left " << n.left() << " right " << n.right();
  return out;
}

std::ostream& operator<<(std::ostream& out, const kvstore_proto::Intention& i)
{
  out << "- intention tree_size = " << i.tree_size() << std::endl;
  for (int idx = 0; idx < i.tree_size(); idx++) {
    out << "  " << idx << ": " << i.tree(idx) << std::endl;
  }
  return out;
}

// a node in an intention contains pointers that are:
//
// 1. nil
// 2. targets outside this intention
// 3. targets within this intention
// 4. targets within this intention to the newly created node
//
// If (1) then csn/off are ignored, so nothing special is required.
//
// If (2) then the pointer was copied from a previous version of the tree,
// in which case the csn/off was also copied over.
//
//    NOTE: need ot make sure this is reflected in the balance/rotate logic
//    so that we aren't JUST copying the shared_ptr.
//
// If (3) then the pointer needs to have its csn set to 0 and its offset
// updated correctly.
//
// if (4), then same as (3).

void DB::serialize_node(kvstore_proto::Node *n, NodeRef node,
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

uint64_t DB::root_id_ = 928734;

void DB::write_dot_null(std::ostream& out,
    NodeRef node, uint64_t& nullcount)
{
  nullcount++;
  out << "null" << nullcount << " [shape=point];"
    << std::endl;
  out << "\"" << node.get() << "\" -> " << "null"
    << nullcount << " [label=\"nil\"];" << std::endl;
}

void DB::write_dot_node(std::ostream& out,
    NodeRef parent, NodePtr& child, const std::string& dir)
{
  out << "\"" << parent.get() << "\":" << dir << " -> ";
  out << "\"" << child.ref.get() << "\"";
  out << " [label=\"" << child.csn << ":"
    << child.offset << "\"];" << std::endl;
}

void DB::write_dot_recursive(std::ostream& out, uint64_t rid,
    NodeRef node, uint64_t& nullcount, bool scoped)
{
  if (scoped && node->rid != rid)
    return;

  out << "\"" << node.get() << "\" ["
    << "label=" << node->elem << ",style=filled,"
    << "fillcolor=" << (node->red ? "red" :
        "black,fontcolor=white")
    << "]" << std::endl;

  if (node->left.ref == DB::Nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->left, "sw");
    write_dot_recursive(out, rid, node->left.ref, nullcount, scoped);
  }

  if (node->right.ref == DB::Nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->right, "se");
    write_dot_recursive(out, rid, node->right.ref, nullcount, scoped);
  }
}

void DB::_write_dot(std::ostream& out, NodeRef root,
    uint64_t& nullcount, bool scoped)
{
  write_dot_recursive(out, root->rid,
      root, nullcount, scoped);
}

void DB::write_dot(std::ostream& out, bool scoped)
{
  uint64_t nullcount = 0;
  out << "digraph ptree {" << std::endl;
  _write_dot(out, roots_.back(), nullcount, scoped);
  out << "}" << std::endl;
}

void DB::write_dot_history(std::ostream& out)
{
  uint64_t trees = 0;
  uint64_t nullcount = 0;
  out << "digraph ptree {" << std::endl;
  for (unsigned i = 1; i < roots_.size(); i++) {
    out << "subgraph cluster_" << trees++ << " {" << std::endl;
    _write_dot(out, roots_[i], nullcount, true);
    out << "}" << std::endl;
  }
  out << "}" << std::endl;
}

NodeRef DB::insert_recursive(std::deque<NodeRef>& path,
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
  auto copy = copy_node(node, rid);

  if (less)
    copy->left.ref = child;
  else
    copy->right.ref = child;

  path.push_back(copy);

  return copy;
}

template<typename ChildA, typename ChildB >
NodeRef DB::rotate(NodeRef parent,
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
void DB::insert_balance(NodeRef& parent, NodeRef& nn,
    std::deque<NodeRef>& path, ChildA child_a, ChildB child_b,
    NodeRef& root, uint64_t rid)
{
  assert(path.front() != DB::Nil());
  NodePtr& uncle = child_b(path.front());
  if (uncle.ref->red) {
    std::cerr << "insert_balance: copy uncle " << uncle.ref << std::endl;
    uncle.ref = copy_node(uncle.ref, rid);
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

void DB::insert(std::string elem)
{
  uint64_t rid = root_id_++;

  std::deque<NodeRef> path;

  auto root = insert_recursive(path, elem, roots_.back(), rid);
  if (root == nullptr)
    return;

  path.push_back(DB::Nil());

  assert(path.size() >= 2);

  auto nn = pop_front(path);
  auto parent = pop_front(path);

  while (parent->red) {
    assert(!path.empty());
    auto grand_parent = path.front();
    if (grand_parent->left.ref == parent)
      insert_balance(parent, nn, path, left, right, root, rid);
    else
      insert_balance(parent, nn, path, right, left, root, rid);
  }

  root->red = false;

  // build an intention for the new tree
  kvstore_proto::Intention intention;
  serialize_intention(intention, root);

  // append to the database log
  std::string blob;
  assert(intention.IsInitialized());
  assert(intention.SerializeToString(&blob));
  db_.push_back(blob);
  uint64_t pos = db_.size() - 1;

  // update the in-memory intention ptrs
  set_intention_self_csn(root, pos);

  std::cerr << intention << std::endl;

  roots_.push_back(root);

  // todo: enable/disable debug mode
  validate_rb_tree();
}

void DB::print_node(NodeRef node)
{
  if (node == DB::Nil())
    std::cout << "nil:" << (node->red ? "r" : "b");
  else
    std::cout << node->elem << ":" << (node->red ? "r" : "b");
}

void DB::print_path(std::deque<NodeRef>& path)
{
  std::cout << "path: ";
  if (path.empty()) {
    std::cout << "<empty>";
  } else {
    std::cout << "[";
    for (auto node : path) {
      if (node == DB::Nil())
        std::cout << "nil:" << (node->red ? "r " : "b ");
      else
        std::cout << node->elem << ":" << (node->red ? "r " : "b ");
    }
    std::cout << "]";
  }
  std::cout << std::endl;
}

bool DB::validate_rb_tree(bool all)
{
  if (all) {
    for (auto root : roots_) {
      if (_validate_rb_tree(root) == 0)
        return false;
    }
    return true;
  }
  return _validate_rb_tree(roots_.back()) != 0;
}

int DB::_validate_rb_tree(NodeRef root)
{
  if (root == DB::Nil())
    return 1;

  NodeRef ln = root->left.ref;
  NodeRef rn = root->right.ref;

  if (root->red && (ln->red || rn->red))
    return 0;

  int lh = _validate_rb_tree(ln);
  int rh = _validate_rb_tree(rn);

  if ((ln != DB::Nil() && ln->elem >= root->elem) ||
      (rn != DB::Nil() && rn->elem <= root->elem))
    return 0;

  if (lh != 0 && rh != 0 && lh != rh)
    return 0;

  if (lh != 0 && rh != 0)
    return root->red ? lh : lh + 1;

  return 0;
}

void DB::serialize_intention_recursive(kvstore_proto::Intention& i,
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

void DB::serialize_intention(kvstore_proto::Intention& i, NodeRef node) {
  int field_index = 0;
  serialize_intention_recursive(i, node->rid, node, field_index);
}

void DB::set_intention_self_csn_recursive(uint64_t rid,
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

void DB::set_intention_self_csn(NodeRef root, uint64_t pos) {
  set_intention_self_csn_recursive(root->rid, root, pos);
}
