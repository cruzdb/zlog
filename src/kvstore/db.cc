#include "db.h"
#include "transaction.h"

DB::DB() :
  cache_(this)
{
  roots_[0] = Node::Nil();

  std::string blob;
  kvstore_proto::Intention intention;
  intention.set_snapshot(-1);
  assert(intention.IsInitialized());
  assert(intention.SerializeToString(&blob));
  log_append(blob);

  last_pos_ = 0;
  stop_ = false;

  // todo: enable/disable debug
  validate_rb_tree();

  log_processor_ = std::thread(&DB::process_log_entry, this);
}

DB::DB(std::vector<std::string> log) :
  cache_(this)
{
  roots_[0] = Node::Nil();

  log_ = log;
  last_pos_ = 0;
  stop_ = false;

  // todo: enable/disable debug
  validate_rb_tree();

  log_processor_ = std::thread(&DB::process_log_entry, this);
}

DB::~DB()
{
  stop_ = true;
  log_cond_.notify_all();
  if (log_processor_.joinable())
    log_processor_.join();
}

std::set<std::string> DB::stl_set(Snapshot snapshot) {
  std::set<std::string> set;
  NodeRef node = snapshot.root;
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
      cache_.ResolveNodePtr(node->right);
      stack.push(node->right.ref);
    }
    if (node->left.ref != Node::Nil()) {
      cache_.ResolveNodePtr(node->left);
      stack.push(node->left.ref);
    }
  }
  return set;
}

std::set<std::string> DB::stl_set() {
  return stl_set(GetSnapshot());
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

  cache_.ResolveNodePtr(node->left);
  cache_.ResolveNodePtr(node->right);

  assert(node->left.ref != nullptr);
  if (node->left.ref == Node::Nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->left, "sw");
    write_dot_recursive(out, rid, node->left.ref, nullcount, scoped);
  }

  assert(node->right.ref != nullptr);
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
  assert(root != nullptr);
  write_dot_recursive(out, root->rid,
      root, nullcount, scoped);
}

void DB::write_dot(std::ostream& out, bool scoped)
{
  auto root = roots_.crbegin();
  assert(root != roots_.crend());
  uint64_t nullcount = 0;
  out << "digraph ptree {" << std::endl;
  _write_dot(out, root->second, nullcount, scoped);
  out << "}" << std::endl;
}

void DB::write_dot_history(std::ostream& out)
{
  uint64_t trees = 0;
  uint64_t nullcount = 0;
  out << "digraph ptree {" << std::endl;
  auto it = roots_.cbegin();
  it++;
  for (; it != roots_.cend(); it++) {
    out << "subgraph cluster_" << trees++ << " {" << std::endl;
    _write_dot(out, it->second, nullcount, true);
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
    for (auto it = roots_.cbegin(); it != roots_.cend(); it++) {
      if (_validate_rb_tree(it->second) == 0)
        return false;
    }
    return true;
  }
  auto root = roots_.crbegin();
  assert(root != roots_.crend());
  return _validate_rb_tree(root->second) != 0;
}

int DB::_validate_rb_tree(NodeRef root)
{
  assert(root != nullptr);

  if (root == Node::Nil())
    return 1;

  cache_.ResolveNodePtr(root->left);
  cache_.ResolveNodePtr(root->right);

  assert(root->left.ref);
  assert(root->right.ref);

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
  auto root = roots_.crbegin();
  assert(root != roots_.crend());
  std::cerr << "begin txn: snapshot " << root->first << std::endl;
  return Transaction(this, root->second, root->first, root_id_++);
}

void DB::process_log_entry()
{
  for (;;) {
    std::unique_lock<std::mutex> l(lock_);
    uint64_t tail = log_tail();

    assert(last_pos_ <= tail);
    if (last_pos_ == tail) {
      log_cond_.wait_for(l, std::chrono::milliseconds(2000));
      if (stop_)
        return;
      continue;
    }

    if (stop_)
      return;

    // process log in strict serial order
    uint64_t next = last_pos_ + 1;
    assert(next <= tail);

    // TODO: intention cache here that sits on top of DB
    // read and deserialize intention from log
    std::string i_snapshot = log_read(next);
    l.unlock();

    kvstore_proto::Intention i;
    assert(i.ParseFromString(i_snapshot));
    assert(i.IsInitialized());

    // meld-subset: only allow serial intentions
    if (i.snapshot() == -1) assert(next == 0);
    if (i.snapshot() != -1) assert(next > 0);
    if (i.snapshot() == (int64_t)last_pos_) {

      auto root = cache_.CacheIntention(i, next);
      roots_[next] = root;

      std::cerr << "commiting serial txn: pos " << next << std::endl;
      l.lock();
      auto res = committed_.emplace(std::make_pair(next, true));
      assert(res.second);
      l.unlock();

    } else {
      std::cerr << "aborting non-serial txn: pos " << next << std::endl;
      l.lock();
      auto res = committed_.emplace(std::make_pair(next, false));
      assert(res.second);
      l.unlock();
    }

    result_cv_.notify_all();

    last_pos_ = next;
  }
}

bool DB::CommitResult(uint64_t pos)
{
  for (;;) {
    std::unique_lock<std::mutex> l(lock_);
    auto it = committed_.find(pos);
    if (it != committed_.end()) {
      return it->second;
    }
    result_cv_.wait(l);
  }
}

size_t DB::log_append(std::string blob)
{
  std::lock_guard<std::mutex> l(log_lock_);
  log_.push_back(blob);
  log_cond_.notify_all();
  return log_.size() - 1;
}

size_t DB::log_tail() {
  std::lock_guard<std::mutex> l(log_lock_);
  return log_.size() - 1;
}

std::vector<std::string> DB::log() {
  std::lock_guard<std::mutex> l(log_lock_);
  return log_;
}

std::string DB::log_read(size_t pos)
{
  std::lock_guard<std::mutex> l(log_lock_);
  return log_.at(pos);
}
