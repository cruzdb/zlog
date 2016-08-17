#include "db_impl.h"
#include <sstream>

DBImpl::DBImpl(zlog::Log *log) :
  log_(log), cache_(this)
{
  root_ = Node::Nil();
  root_pos_ = 0;

  last_pos_ = 0;
  stop_ = false;

  // todo: enable/disable debug
  validate_rb_tree(root_);

  log_processor_ = std::thread(&DBImpl::process_log_entry, this);
}

int DB::Open(zlog::Log *log, bool create_if_empty, DB **db)
{
  uint64_t tail;
  int ret = log->CheckTail(&tail);
  assert(ret == 0);

  // empty log
  if (tail == 0) {
    if (!create_if_empty)
      return -EINVAL;

    std::string blob;
    kvstore_proto::Intention intention;
    intention.set_snapshot(-1);
    assert(intention.IsInitialized());
    assert(intention.SerializeToString(&blob));

    ret = log->Append(blob, &tail);
    assert(ret == 0);
    assert(tail == 0);

    ret = log->CheckTail(&tail);
    assert(ret == 0);
    assert(tail == 1);
  }

  DBImpl *impl = new DBImpl(log);
  *db = impl;

  return 0;
}

DB::~DB()
{
}

DBImpl::~DBImpl()
{
  lock_.lock();
  stop_ = true;
  log_cond_.notify_all();
  lock_.unlock();
  log_processor_.join();
}

std::ostream& operator<<(std::ostream& out, const NodeRef& n)
{
  out << "node(" << n.get() << "):" << n->key() << ": ";
  out << (n->red() ? "red " : "blk ");
  out << "fi " << n->field_index() << " ";
  out << "left=[p" << n->left.csn() << ",o" << n->left.offset() << ",";
  if (n->left.ref() == Node::Nil())
    out << "nil";
  else
    out << n->left.ref().get();
  out << "] ";
  out << "right=[p" << n->right.csn() << ",o" << n->right.offset() << ",";
  if (n->right.ref() == Node::Nil())
    out << "nil";
  else
    out << n->right.ref().get();
  out << "] ";
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
  out << "key " << n.key() << " val " << n.val() << " ";
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

uint64_t DBImpl::root_id_ = 928734;

void DBImpl::write_dot_null(std::ostream& out,
    NodeRef node, uint64_t& nullcount)
{
  nullcount++;
  out << "null" << nullcount << " [shape=point];"
    << std::endl;
  out << "\"" << node.get() << "\" -> " << "null"
    << nullcount << " [label=\"nil\"];" << std::endl;
}

void DBImpl::write_dot_node(std::ostream& out,
    NodeRef parent, NodePtr& child, const std::string& dir)
{
  out << "\"" << parent.get() << "\":" << dir << " -> ";
  out << "\"" << child.ref().get() << "\"";
  out << " [label=\"" << child.csn() << ":"
    << child.offset() << "\"];" << std::endl;
}

void DBImpl::write_dot_recursive(std::ostream& out, uint64_t rid,
    NodeRef node, uint64_t& nullcount, bool scoped)
{
  if (scoped && node->rid() != rid)
    return;

  out << "\"" << node.get() << "\" ["
    << "label=\"" << node->key() << "_" << node->val() << "\",style=filled,"
    << "fillcolor=" << (node->red() ? "red" :
        "black,fontcolor=white")
    << "]" << std::endl;

  assert(node->left.ref() != nullptr);
  if (node->left.ref() == Node::Nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->left, "sw");
    write_dot_recursive(out, rid, node->left.ref(), nullcount, scoped);
  }

  assert(node->right.ref() != nullptr);
  if (node->right.ref() == Node::Nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->right, "se");
    write_dot_recursive(out, rid, node->right.ref(), nullcount, scoped);
  }
}

void DBImpl::_write_dot(std::ostream& out, NodeRef root,
    uint64_t& nullcount, bool scoped)
{
  assert(root != nullptr);
  write_dot_recursive(out, root->rid(),
      root, nullcount, scoped);
}

void DBImpl::write_dot(std::ostream& out, bool scoped)
{
  auto root = root_;
  uint64_t nullcount = 0;
  out << "digraph ptree {" << std::endl;
  _write_dot(out, root, nullcount, scoped);
  out << "}" << std::endl;
}

void DBImpl::write_dot_history(std::ostream& out,
    std::vector<Snapshot*>& snapshots)
{
  uint64_t trees = 0;
  uint64_t nullcount = 0;
  out << "digraph ptree {" << std::endl;
  std::string prev_root = "";

  for (auto it = snapshots.cbegin(); it != snapshots.end(); it++) {

    // build sub-graph label
    std::stringstream label;
    label << "label = \"root: " << (*it)->seq;
    for (const auto& s : (*it)->desc)
      label << "\n" << s;
    label << "\"";

    out << "subgraph cluster_" << trees++ << " {" << std::endl;
    if ((*it)->root == Node::Nil()) {
      out << "null" << ++nullcount << " [label=nil];" << std::endl;
    } else {
      _write_dot(out, (*it)->root, nullcount, true);
    }

#if 0
    if (prev_root != "")
      out << "\"" << prev_root << "\" -> \"" << it->root.get() << "\" [style=invis];" << std::endl;
    std::stringstream ss;
    ss << it->root.get();
    prev_root = ss.str();
#endif
    out << label.str() << std::endl;
    out << "}" << std::endl;
  }
  out << "}" << std::endl;
}

void DBImpl::print_node(NodeRef node)
{
  if (node == Node::Nil())
    std::cout << "nil:" << (node->red() ? "r" : "b");
  else
    std::cout << node->key() << ":" << (node->red() ? "r" : "b");
}

void DBImpl::print_path(std::ostream& out, std::deque<NodeRef>& path)
{
  out << "path: ";
  if (path.empty()) {
    out << "<empty>";
  } else {
    out << "[";
    for (auto node : path) {
      if (node == Node::Nil())
        out << "nil:" << (node->red() ? "r " : "b ");
      else
        out << node->key() << ":" << (node->red() ? "r " : "b ");
    }
    out << "]";
  }
  out << std::endl;
}

/*
 *
 */
int DBImpl::_validate_rb_tree(const NodeRef root)
{
  assert(root != nullptr);

  assert(root->read_only());
  if (!root->read_only())
    return 0;

  if (root == Node::Nil())
    return 1;

  assert(root->left.ref());
  assert(root->right.ref());

  NodeRef ln = root->left.ref();
  NodeRef rn = root->right.ref();

  if (root->red() && (ln->red() || rn->red()))
    return 0;

  int lh = _validate_rb_tree(ln);
  int rh = _validate_rb_tree(rn);

  if ((ln != Node::Nil() && ln->key() >= root->key()) ||
      (rn != Node::Nil() && rn->key() <= root->key()))
    return 0;

  if (lh != 0 && rh != 0 && lh != rh)
    return 0;

  if (lh != 0 && rh != 0)
    return root->red() ? lh : lh + 1;

  return 0;
}

void DBImpl::validate_rb_tree(NodeRef root)
{
  assert(_validate_rb_tree(root) != 0);
}

Transaction *DBImpl::BeginTransaction()
{
  std::lock_guard<std::mutex> l(lock_);
  return new TransactionImpl(this, root_, root_pos_, root_id_++);
}

void DBImpl::process_log_entry()
{
  for (;;) {
    std::unique_lock<std::mutex> l(lock_);

    if (stop_)
      return;

    uint64_t tail;
    int ret = log_->CheckTail(&tail);
    assert(ret == 0);

    assert(last_pos_ < tail);

    if ((last_pos_ + 1) == tail) {
      log_cond_.wait(l);
      continue; // try again
    }

    // process log in strict serial order
    uint64_t next = last_pos_ + 1;
    assert(next < tail);

    // read and deserialize intention from log
    std::string i_snapshot;
    ret = log_->Read(next, &i_snapshot);
    assert(ret == 0);

    kvstore_proto::Intention i;
    assert(i.ParseFromString(i_snapshot));
    assert(i.IsInitialized());

    // meld-subset: only allow serial intentions
    if (i.snapshot() == -1) assert(next == 0);
    if (i.snapshot() != -1) assert(next > 0);
    if (i.snapshot() == (int64_t)last_pos_) {
      auto root = cache_.CacheIntention(i, next);
      validate_rb_tree(root);
      root_ = root;
      root_pos_ = next;

      root_desc_.clear();
      for (int idx = 0; idx < i.description_size(); idx++)
        root_desc_.push_back(i.description(idx));

      auto res = committed_.emplace(std::make_pair(next, true));
      assert(res.second);
    } else {
      auto res = committed_.emplace(std::make_pair(next, false));
      assert(res.second);
    }

    result_cv_.notify_all();

    last_pos_ = next;
  }
}

bool DBImpl::CommitResult(uint64_t pos)
{
  for (;;) {
    std::unique_lock<std::mutex> l(lock_);
    auto it = committed_.find(pos);
    if (it != committed_.end()) {
      bool ret = it->second;
      committed_.erase(it);
      return ret;
    }
    result_cv_.wait(l);
  }
}
