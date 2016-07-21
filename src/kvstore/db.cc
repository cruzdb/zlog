#include "db.h"
#include "transaction.h"

DB::DB()
{
  roots_.push_back(Node::Nil());

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
  if (node == Node::Nil())
    return set;
  std::stack<NodeRef> stack;
  stack.push(node);
  while (!stack.empty()) {
    node = stack.top();
    stack.pop();
    auto ret = set.emplace(node->elem);
    assert(ret.second);
    if (node->right.ref != Node::Nil()) {
      if (node->right.ref == nullptr)
        node_cache_get_(node->right);
      stack.push(node->right.ref);
    }
    if (node->left.ref != Node::Nil()) {
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

  if (node->left.ref == Node::Nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->left, "sw");
    write_dot_recursive(out, rid, node->left.ref, nullcount, scoped);
  }

  if (node->right.ref == Node::Nil())
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

void DB::print_node(NodeRef node)
{
  if (node == Node::Nil())
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
      if (node == Node::Nil())
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
  if (root == Node::Nil())
    return 1;

  NodeRef ln = root->left.ref;
  NodeRef rn = root->right.ref;

  if (root->red && (ln->red || rn->red))
    return 0;

  int lh = _validate_rb_tree(ln);
  int rh = _validate_rb_tree(rn);

  if ((ln != Node::Nil() && ln->elem >= root->elem) ||
      (rn != Node::Nil() && rn->elem <= root->elem))
    return 0;

  if (lh != 0 && rh != 0 && lh != rh)
    return 0;

  if (lh != 0 && rh != 0)
    return root->red ? lh : lh + 1;

  return 0;
}

Transaction DB::BeginTransaction()
{
  return Transaction(this, roots_.back(), root_id_++);
}
