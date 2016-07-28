#include "node_cache.h"
#include "db.h"

void NodeCache::ResolveNodePtr(NodePtr& ptr)
{
  if (ptr.ref != nullptr)
    return;

  auto it = nodes_.find(std::make_pair(ptr.csn, ptr.offset));
  if (it != nodes_.end()) {
    ptr.ref = it->second;
    return;
  }

  // the cache sits on top of the database log
  std::string snapshot = db_->log_read(ptr.csn);
  kvstore_proto::Intention i;
  assert(i.ParseFromString(snapshot));
  assert(i.IsInitialized());

  auto nn = deserialize_node(i, ptr.csn, ptr.offset);

  assert(nn->read_only());
  nodes_.insert(std::make_pair(
        std::make_pair(ptr.csn, ptr.offset), nn));

  ptr.ref = nn;
}

NodeRef NodeCache::CacheIntention(const kvstore_proto::Intention& i,
    uint64_t pos)
{
  if (i.tree_size() == 0)
    return Node::Nil();

  NodeRef nn = nullptr;
  for (int idx = 0; idx < i.tree_size(); idx++) {
    nn = deserialize_node(i, pos, idx);

    assert(nn->read_only());
    nodes_.insert(std::make_pair(std::make_pair(pos, idx), nn));
  }

  assert(nn != nullptr);
  return nn; // root is last node in intention
}

NodeRef NodeCache::deserialize_node(const kvstore_proto::Intention& i,
    uint64_t pos, int index)
{
  const kvstore_proto::Node& n = i.tree(index);

  // TODO: replace rid==csn with a lookup table that lets us
  // use random values for more reliable assertions.
  //
  // TODO: initialize so it can be read-only after creation
  auto nn = std::make_shared<Node>(n.key(), n.val(), n.red(),
      Node::Nil(), Node::Nil(), pos, index, false);

  assert(nn->field_index() == index);
  if (!n.left().nil()) {
    nn->left.ref = nullptr;
    nn->left.offset = n.left().off();
    if (n.left().self()) {
      nn->left.csn = pos;
    } else {
      nn->left.csn = n.left().csn();
    }
    ResolveNodePtr(nn->left);
  }

  if (!n.right().nil()) {
    nn->right.ref = nullptr;
    nn->right.offset = n.right().off();
    if (n.right().self()) {
      nn->right.csn = pos;
    } else {
      nn->right.csn = n.right().csn();
    }
    ResolveNodePtr(nn->right);
  }

  nn->set_read_only();

  return nn;
}
