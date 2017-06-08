#include "db_impl.h"
#include <sstream>

DBImpl::DBImpl(zlog::Log *log) :
  log_(log),
  cache_(this),
  stop_(false),
  root_id_(-1),
  root_(Node::Nil(), this, true),
  cur_txn_(nullptr),
  txn_finisher_(std::thread(&DBImpl::TransactionFinisher, this))
{
  validate_rb_tree(root_);
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
  }

  DBImpl *impl = new DBImpl(log);
  ret = impl->RestoreFromLog();
  if (ret)
    return ret;

  *db = impl;

  return 0;
}

DB::~DB()
{
}

DBImpl::~DBImpl()
{
  {
    std::lock_guard<std::mutex> l(lock_);
    stop_ = true;
  }
  txn_finisher_cond_.notify_one();
  txn_finisher_.join();
  cache_.Stop();
}

int DBImpl::RestoreFromLog()
{
  uint64_t tail;
  int ret = log_->CheckTail(&tail);
  assert(ret == 0);

  std::string data;
  while (true) {
    ret = log_->Read(tail, &data);
    if (tail == 0 || ret == 0)
      break;
    tail--;
  }

  kvstore_proto::Intention i;
  assert(i.ParseFromString(data));
  assert(i.IsInitialized());
  auto root = cache_.CacheIntention(i, tail);
  root_.replace(root);

  return 0;
}

std::ostream& operator<<(std::ostream& out, const SharedNodeRef& n)
{
  out << "node(" << n.get() << "):" << n->key().ToString() << ": ";
  out << (n->red() ? "red " : "blk ");
  //out << "fi " << n->field_index() << " ";
  out << "left=[p" << n->left.csn() << ",o" << n->left.offset() << ",";
  if (n->left.ref_notrace() == Node::Nil())
    out << "nil";
  else
    out << n->left.ref_notrace().get();
  out << "] ";
  out << "right=[p" << n->right.csn() << ",o" << n->right.offset() << ",";
  if (n->right.ref_notrace() == Node::Nil())
    out << "nil";
  else
    out << n->right.ref_notrace().get();
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

void DBImpl::write_dot_null(std::ostream& out,
    SharedNodeRef node, uint64_t& nullcount)
{
  nullcount++;
  out << "null" << nullcount << " [shape=point];"
    << std::endl;
  out << "\"" << node.get() << "\" -> " << "null"
    << nullcount << " [label=\"nil\"];" << std::endl;
}

void DBImpl::write_dot_node(std::ostream& out,
    SharedNodeRef parent, NodePtr& child, const std::string& dir)
{
  out << "\"" << parent.get() << "\":" << dir << " -> ";
  out << "\"" << child.ref_notrace().get() << "\"";
  out << " [label=\"" << child.csn() << ":"
    << child.offset() << "\"];" << std::endl;
}

void DBImpl::write_dot_recursive(std::ostream& out, int64_t rid,
    SharedNodeRef node, uint64_t& nullcount, bool scoped)
{
  if (scoped && node->rid() != rid)
    return;

  out << "\"" << node.get() << "\" ["
    << "label=\"" << node->key().ToString() << "_" << node->val().ToString() << "\",style=filled,"
    << "fillcolor=" << (node->red() ? "red" :
        "black,fontcolor=white")
    << "]" << std::endl;

  assert(node->left.ref_notrace() != nullptr);
  if (node->left.ref_notrace() == Node::Nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->left, "sw");
    write_dot_recursive(out, rid, node->left.ref_notrace(), nullcount, scoped);
  }

  assert(node->right.ref_notrace() != nullptr);
  if (node->right.ref_notrace() == Node::Nil())
    write_dot_null(out, node, nullcount);
  else {
    write_dot_node(out, node, node->right, "se");
    write_dot_recursive(out, rid, node->right.ref_notrace(), nullcount, scoped);
  }
}

void DBImpl::_write_dot(std::ostream& out, SharedNodeRef root,
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
  _write_dot(out, root.ref_notrace(), nullcount, scoped);
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
    label << "label = \"root: " << (*it)->root.csn();
    label << "\"";

    out << "subgraph cluster_" << trees++ << " {" << std::endl;
    auto ref = (*it)->root.ref_notrace();
    if (ref == Node::Nil()) {
      out << "null" << ++nullcount << " [label=nil];" << std::endl;
    } else {
      _write_dot(out, ref, nullcount, true);
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

void DBImpl::print_node(SharedNodeRef node)
{
  if (node == Node::Nil())
    std::cout << "nil:" << (node->red() ? "r" : "b");
  else
    std::cout << node->key().ToString() << ":" << (node->red() ? "r" : "b");
}

void DBImpl::print_path(std::ostream& out, std::deque<SharedNodeRef>& path)
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
        out << node->key().ToString() << ":" << (node->red() ? "r " : "b ");
    }
    out << "]";
  }
  out << std::endl;
}

/*
 *
 */
int DBImpl::_validate_rb_tree(const SharedNodeRef root)
{
  assert(root != nullptr);

  assert(root->read_only());
  if (!root->read_only())
    return 0;

  if (root == Node::Nil())
    return 1;

  assert(root->left.ref_notrace());
  assert(root->right.ref_notrace());

  SharedNodeRef ln = root->left.ref_notrace();
  SharedNodeRef rn = root->right.ref_notrace();

  if (root->red() && (ln->red() || rn->red()))
    return 0;

  int lh = _validate_rb_tree(ln);
  int rh = _validate_rb_tree(rn);

  if ((ln != Node::Nil() && ln->key().compare(root->key()) >= 0) ||
      (rn != Node::Nil() && rn->key().compare(root->key()) <= 0))
    return 0;

  if (lh != 0 && rh != 0 && lh != rh)
    return 0;

  if (lh != 0 && rh != 0)
    return root->red() ? lh : lh + 1;

  return 0;
}

void DBImpl::validate_rb_tree(NodePtr root)
{
  assert(_validate_rb_tree(root.ref_notrace()) != 0);
}

/*
 * TODO:
 *  - we way want to add a policy that allows a long-running transaction to be
 *  forced to abort so that it doesn't hold up other transactions waiting.
 */
Transaction *DBImpl::BeginTransaction()
{
  std::unique_lock<std::mutex> lk(lock_);
  while (true) {
    if (cur_txn_ == nullptr) {
      cur_txn_ = new TransactionImpl(this, root_, root_id_--);
      return cur_txn_;
    } else {
      cur_txn_cond_.wait(lk);
    }
  }
}

void DBImpl::TransactionFinisher()
{
  while (true) {
    std::unique_lock<std::mutex> lk(lock_);

    if (stop_)
      return;

    if (!cur_txn_ || !cur_txn_->Committed()) {
      txn_finisher_cond_.wait(lk);
      continue;
    }

    // serialize the after image
    kvstore_proto::Intention i;
    std::vector<SharedNodeRef> delta;
    cur_txn_->SerializeAfterImage(i, delta);

    std::string blob;
    assert(i.IsInitialized());
    assert(i.SerializeToString(&blob));

    // append after image to the log
    uint64_t pos;
    int ret = log_->Append(blob, &pos);
    assert(ret == 0);

    // apply the log position to the after image nodes
    cur_txn_->SetDeltaPosition(delta, pos);

    // fold afterimage into node cache and update db root
    auto root = cache_.ApplyAfterImageDelta(delta, pos);
    root_.replace(root);

    // mark complete
    cur_txn_->MarkComplete();
    cur_txn_ = nullptr;

    lk.unlock();
    cur_txn_cond_.notify_one();
  }
}

void DBImpl::AbortTransaction(TransactionImpl *txn)
{
  assert(txn == cur_txn_);
  assert(!txn->Committed());
  assert(!txn->Completed());

  lock_.lock();
  cur_txn_ = nullptr;
  lock_.unlock();

  cur_txn_cond_.notify_one();
}

void DBImpl::CompleteTransaction(TransactionImpl *txn)
{
  assert(txn == cur_txn_);
  assert(!txn->Committed());
  assert(!txn->Completed());

  // it's important to mark the txn as committed while holding this lock
  // because the committed state is examined before blocking on a condition
  // variable in the txn finisher thread. otherwise there is a race that will
  // cause the finisher to miss the state change and wakeup.
  lock_.lock();
  cur_txn_->MarkCommitted();
  lock_.unlock();

  // notify txn finisher
  txn_finisher_cond_.notify_one();
}
