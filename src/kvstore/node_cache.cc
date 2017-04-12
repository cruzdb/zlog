#include "node_cache.h"
#include "db_impl.h"
#include <time.h>
#include <deque>
#include <condition_variable>

// TODO: if usage goes above high marker block new txns
static const size_t low_marker  =  4*1024*1024;
//static const size_t high_marker = 8*1024*1024;

void NodeCache::do_vaccum_()
{
  while (true) {
    std::unique_lock<std::mutex> l(lock_);

    cond_.wait(l, [this]{
        return !traces_.empty() || UsedBytes() > low_marker || stop_;
    });

    if (stop_)
      return;

    // apply lru updates
    for (auto trace : traces_) {
      for (auto key : trace) {
        auto node_it = nodes_.find(key);
        if (node_it == nodes_.end())
          continue;
        entry& e = node_it->second;
        nodes_lru_.erase(e.lru_iter);
        nodes_lru_.emplace_front(key);
        e.lru_iter = nodes_lru_.begin();
      }
    }
    traces_.clear();

    while (UsedBytes() > low_marker) {
      assert(!nodes_lru_.empty());
      auto key = nodes_lru_.back();
      auto nit = nodes_.find(key);
      assert(nit != nodes_.end());
      used_bytes_ -= nit->second.node->ByteSize();
      nodes_.erase(nit);
      nodes_lru_.pop_back();
    }
  }
}

// when resolving a node we only resolve the single node. figuring out when to
// resolve an entire intention would be interesting.
SharedNodeRef NodeCache::fetch(std::vector<std::pair<int64_t, int>>& trace,
    int64_t csn, int offset)
{
  std::lock_guard<std::mutex> l(lock_);

  // update traces since we already have the lock. more importantly, we want
  // to update the traces here because if we have a cache hit below we'll need
  // to go to storage to resolve the pointer.
  if (!trace.empty()) {
    traces_.emplace_front();
    traces_.front().swap(trace);
    cond_.notify_one();
  }

  auto key = std::make_pair(csn, offset);

  // lru update
  auto it = nodes_.find(key);
  if (it != nodes_.end()) {
    entry& e = it->second;
    nodes_lru_.erase(e.lru_iter);
    nodes_lru_.emplace_front(key);
    e.lru_iter = nodes_lru_.begin();
    return e.node;
  }

  std::string snapshot;
  int ret = db_->log_->Read(csn, &snapshot);
  assert(ret == 0);

  kvstore_proto::Intention i;
  assert(i.ParseFromString(snapshot));
  assert(i.IsInitialized());

  auto nn = deserialize_node(i, csn, offset);

  assert(nn->read_only());

  used_bytes_ += nn->ByteSize();
  nodes_lru_.emplace_front(key);
  auto iter = nodes_lru_.begin();
  auto res = nodes_.insert(
      std::make_pair(key, entry{nn, iter}));
  assert(res.second);

  return nn;
}

// only resolve to cached nodes when deserializing a cache intention when
// rolling the log forward. other nodes will be resolved on demand
void NodeCache::ResolveNodePtr(NodePtr& ptr)
{
  auto key = std::make_pair(ptr.csn(), ptr.offset());
  auto node_it = nodes_.find(key);
  if (node_it == nodes_.end())
    return;

  // lru update
  entry& e = node_it->second;
  nodes_lru_.erase(e.lru_iter);
  nodes_lru_.emplace_front(key);
  e.lru_iter = nodes_lru_.begin();

  ptr.set_ref(e.node);
}

NodePtr NodeCache::CacheIntention(const kvstore_proto::Intention& i,
    uint64_t pos)
{
  std::lock_guard<std::mutex> l(lock_);

  if (i.tree_size() == 0) {
    NodePtr ret(Node::Nil(), nullptr, true);
    return ret;
  }

  SharedNodeRef nn = nullptr;
  for (int idx = 0; idx < i.tree_size(); idx++) {
    nn = deserialize_node(i, pos, idx);

    assert(nn->read_only());

    used_bytes_ += nn->ByteSize();
    auto key = std::make_pair(pos, idx);
    nodes_lru_.emplace_front(key);
    auto iter = nodes_lru_.begin();
    auto res = nodes_.insert(
        std::make_pair(key, entry{nn, iter}));
    assert(res.second);
  }

  assert(nn != nullptr);
  NodePtr ret(nn, db_, false);
  ret.set_csn(pos);
  ret.set_offset(nn->field_index());
  ret.set_read_only();
  return ret;
}

SharedNodeRef NodeCache::deserialize_node(const kvstore_proto::Intention& i,
    uint64_t pos, int index)
{
  const kvstore_proto::Node& n = i.tree(index);

  // TODO: replace rid==csn with a lookup table that lets us
  // use random values for more reliable assertions.
  //
  // TODO: initialize so it can be read-only after creation
  auto nn = std::make_shared<Node>(n.key(), n.val(), n.red(),
      nullptr, nullptr, pos, index, false, db_);

  // the left and right pointers are undefined. make sure to handle the case
  // correctly in which a child is nil vs defined on storage but not resolved
  // into the heap.

  assert(nn->field_index() == index);
  if (!n.left().nil()) {
    nn->left.set_offset(n.left().off());
    if (n.left().self()) {
      nn->left.set_csn(pos);
    } else {
      nn->left.set_csn(n.left().csn());
    }
    ResolveNodePtr(nn->left);
  } else {
    nn->left.set_ref(Node::Nil());
  }

  if (!n.right().nil()) {
    nn->right.set_offset(n.right().off());
    if (n.right().self()) {
      nn->right.set_csn(pos);
    } else {
      nn->right.set_csn(n.right().csn());
    }
    ResolveNodePtr(nn->right);
  } else {
    nn->right.set_ref(Node::Nil());
  }

  nn->set_read_only();

  return nn;
}
