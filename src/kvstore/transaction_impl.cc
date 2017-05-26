#include <deque>
#include <sstream>
#include "db_impl.h"

void TransactionImpl::UpdateLRU()
{
  db_->UpdateLRU(trace_);
}

void TransactionImpl::serialize_node_ptr(kvstore_proto::NodePtr *dst,
    NodePtr& src, int maybe_offset)
{
  if (src.ref(trace_) == Node::Nil()) {
    dst->set_nil(true);
    dst->set_self(false);
    dst->set_csn(0);
    dst->set_off(0);
  } else if (src.ref(trace_)->rid() == rid_) {
    dst->set_nil(false);
    dst->set_self(true);
    dst->set_csn(0);
    dst->set_off(maybe_offset);
    src.set_offset(maybe_offset); // move up a level
  } else {
    assert(src.ref(trace_) != nullptr);
    dst->set_nil(false);
    dst->set_self(false);
    dst->set_csn(src.csn());
    dst->set_off(src.offset());
  }
}

void TransactionImpl::serialize_node(kvstore_proto::Node *dst,
    SharedNodeRef node, int maybe_left_offset, int maybe_right_offset)
{
  dst->set_red(node->red());
  dst->set_key(node->key().ToString());
  dst->set_val(node->val().ToString());

  serialize_node_ptr(dst->mutable_left(), node->left, maybe_left_offset);
  serialize_node_ptr(dst->mutable_right(), node->right, maybe_right_offset);
}

SharedNodeRef TransactionImpl::insert_recursive(std::deque<SharedNodeRef>& path,
    const Slice& key, const Slice& value, const SharedNodeRef& node)
{
  assert(node != nullptr);

  if (node == Node::Nil()) {
    auto nn = std::make_shared<Node>(key, value, true, Node::Nil(),
        Node::Nil(), rid_, false, db_);
    path.push_back(nn);
    fresh_nodes_.push_back(nn);
    return nn;
  }

  int cmp = key.compare(Slice(node->key().data(),
        node->key().size()));
  bool less = cmp < 0;
  bool equal = cmp == 0;

  /*
   * How should we handle key/value updates? What about when the values are
   * the same?
   */
  if (equal)
    return nullptr;

  auto child = insert_recursive(path, key, value,
      (less ? node->left.ref(trace_) : node->right.ref(trace_)));

  if (child == nullptr)
    return child;

  /*
   * the copy_node operation will copy the child node references, as well as
   * the csn/offset for each child node reference. however below the reference
   * is updated without updating the csn/offset, which are fixed later when
   * the intention is build.
   */
  SharedNodeRef copy;
  if (node->rid() == rid_)
    copy = node;
  else {
    copy = Node::Copy(node, db_, rid_);
    fresh_nodes_.push_back(copy);
  }

  if (less)
    copy->left.set_ref(child);
  else
    copy->right.set_ref(child);

  path.push_back(copy);

  return copy;
}

template<typename ChildA, typename ChildB >
SharedNodeRef TransactionImpl::rotate(SharedNodeRef parent,
    SharedNodeRef child, ChildA child_a, ChildB child_b, SharedNodeRef& root)
{
  // copy over ref and csn/off because we might be moving a pointer that
  // points outside of the current intentino.
  NodePtr grand_child = child_b(child); // copy constructor makes grand_child read-only
  child_b(child) = child_a(grand_child.ref(trace_));

  if (root == child) {
    root = grand_child.ref(trace_);
  } else if (child_a(parent).ref(trace_) == child)
    child_a(parent) = grand_child;
  else
    child_b(parent) = grand_child;

  // we do not update csn/off here because child is always a pointer to a node
  // in the current intention so its csn/off will be updated during intention
  // serialization step.
  assert(child->rid() == rid_);
  child_a(grand_child.ref(trace_)).set_ref(child);

  return grand_child.ref(trace_);
}

template<typename ChildA, typename ChildB>
void TransactionImpl::insert_balance(SharedNodeRef& parent, SharedNodeRef& nn,
    std::deque<SharedNodeRef>& path, ChildA child_a, ChildB child_b,
    SharedNodeRef& root)
{
  assert(path.front() != Node::Nil());
  NodePtr& uncle = child_b(path.front());
  if (uncle.ref(trace_)->red()) {
    if (uncle.ref(trace_)->rid() != rid_) {
      auto n = Node::Copy(uncle.ref(trace_), db_, rid_);
      fresh_nodes_.push_back(n);
      uncle.set_ref(n);
    }
    parent->set_red(false);
    uncle.ref(trace_)->set_red(false);
    path.front()->set_red(true);
    nn = pop_front(path);
    parent = pop_front(path);
  } else {
    if (nn == child_b(parent).ref(trace_)) {
      std::swap(nn, parent);
      rotate(path.front(), nn, child_a, child_b, root);
    }
    auto grand_parent = pop_front(path);
    grand_parent->swap_color(parent);
    rotate(path.front(), grand_parent, child_b, child_a, root);
  }
}

SharedNodeRef TransactionImpl::delete_recursive(std::deque<SharedNodeRef>& path,
    const Slice& key, const SharedNodeRef& node)
{
  assert(node != nullptr);

  if (node == Node::Nil()) {
    return nullptr;
  }

  int cmp = key.compare(Slice(node->key().data(),
        node->key().size()));
  bool less = cmp < 0;
  bool equal = cmp == 0;

  if (equal) {
    SharedNodeRef copy;
    if (node->rid() == rid_)
      copy = node;
    else {
      copy = Node::Copy(node, db_, rid_);
      fresh_nodes_.push_back(copy);
    }
    path.push_back(copy);
    return copy;
  }

  auto child = delete_recursive(path, key,
      (less ? node->left.ref(trace_) : node->right.ref(trace_)));

  if (child == nullptr) {
    return child;
  }

  /*
   * the copy_node operation will copy the child node references, as well as
   * the csn/offset for each child node reference. however below the reference
   * is updated without updating the csn/offset, which are fixed later when
   * the intention is build.
   */
  SharedNodeRef copy;
  if (node->rid() == rid_)
    copy = node;
  else {
    copy = Node::Copy(node, db_, rid_);
    fresh_nodes_.push_back(copy);
  }

  if (less)
    copy->left.set_ref(child);
  else
    copy->right.set_ref(child);

  path.push_back(copy);

  return copy;
}

void TransactionImpl::transplant(SharedNodeRef parent, SharedNodeRef removed,
    SharedNodeRef transplanted, SharedNodeRef& root)
{
  if (parent == Node::Nil()) {
    root = transplanted;
  } else if (parent->left.ref(trace_) == removed) {
    parent->left.set_ref(transplanted);
  } else {
    parent->right.set_ref(transplanted);
  }
}

SharedNodeRef TransactionImpl::build_min_path(SharedNodeRef node, std::deque<SharedNodeRef>& path)
{
  assert(node != nullptr);
  assert(node->left.ref(trace_) != nullptr);
  while (node->left.ref(trace_) != Node::Nil()) {
    assert(node->left.ref(trace_) != nullptr);
    if (node->left.ref(trace_)->rid() != rid_) {
      auto n = Node::Copy(node->left.ref(trace_), db_, rid_);
      fresh_nodes_.push_back(n);
      node->left.set_ref(n);
    }
    path.push_front(node);
    node = node->left.ref(trace_);
    assert(node != nullptr);
  }
  return node;
}

template<typename ChildA, typename ChildB>
void TransactionImpl::mirror_remove_balance(SharedNodeRef& extra_black, SharedNodeRef& parent,
    std::deque<SharedNodeRef>& path, ChildA child_a, ChildB child_b, SharedNodeRef& root)
{
  SharedNodeRef brother = child_b(parent).ref(trace_);

  if (brother->red()) {
    if (brother->rid() != rid_) {
      auto n = Node::Copy(brother, db_, rid_);
      fresh_nodes_.push_back(n);
      child_b(parent).set_ref(n);
    } else
      child_b(parent).set_ref(brother);
    brother = child_b(parent).ref(trace_);

    brother->swap_color(parent);
    rotate(path.front(), parent, child_a, child_b, root);
    path.push_front(brother);

    brother = child_b(parent).ref(trace_);
  }

  assert(brother != nullptr);

  assert(brother->left.ref(trace_) != nullptr);
  assert(brother->right.ref(trace_) != nullptr);

  if (!brother->left.ref(trace_)->red() && !brother->right.ref(trace_)->red()) {
    if (brother->rid() != rid_) {
      auto n = Node::Copy(brother, db_, rid_);
      fresh_nodes_.push_back(n);
      child_b(parent).set_ref(n);
    } else
      child_b(parent).set_ref(brother);
    brother = child_b(parent).ref(trace_);

    brother->set_red(true);
    extra_black = parent;
    parent = pop_front(path);
  } else {
    if (!child_b(brother).ref(trace_)->red()) {
      if (brother->rid() != rid_) {
        auto n = Node::Copy(brother, db_, rid_);
        fresh_nodes_.push_back(n);
        child_b(parent).set_ref(n);
      } else
        child_b(parent).set_ref(brother);
      brother = child_b(parent).ref(trace_);

      if (child_a(brother).ref(trace_)->rid() != rid_) {
        auto n = Node::Copy(child_a(brother).ref(trace_), db_, rid_);
        fresh_nodes_.push_back(n);
        child_a(brother).set_ref(n);
      }
      brother->swap_color(child_a(brother).ref(trace_));
      brother = rotate(parent, brother, child_b, child_a, root);
    }

    if (brother->rid() != rid_) {
      auto n = Node::Copy(brother, db_, rid_);
      fresh_nodes_.push_back(n);
      child_b(parent).set_ref(n);
    } else
      child_b(parent).set_ref(brother);
    brother = child_b(parent).ref(trace_);

    if (child_b(brother).ref(trace_)->rid() != rid_) {
      auto n = Node::Copy(child_b(brother).ref(trace_), db_, rid_);
      fresh_nodes_.push_back(n);
      child_b(brother).set_ref(n);
    }
    brother->set_red(parent->red());
    parent->set_red(false);
    child_b(brother).ref(trace_)->set_red(false);
    rotate(path.front(), parent, child_a, child_b, root);

    extra_black = root;
    parent = Node::Nil();
  }
}

void TransactionImpl::balance_delete(SharedNodeRef extra_black,
    std::deque<SharedNodeRef>& path, SharedNodeRef& root)
{
  auto parent = pop_front(path);

  assert(extra_black != nullptr);
  assert(root != nullptr);
  assert(parent != nullptr);

  //db_->cache_.ResolveNodePtr(parent->left);
  //assert(parent->left.ref() != nullptr);

  while (extra_black != root && !extra_black->red()) {
    if (parent->left.ref(trace_) == extra_black)
      mirror_remove_balance(extra_black, parent, path, left, right, root);
    else
      mirror_remove_balance(extra_black, parent, path, right, left, root);
  }

  SharedNodeRef new_node;
  if (extra_black->rid() == rid_)
    new_node = extra_black;
  else {
    new_node = Node::Copy(extra_black, db_, rid_);
    fresh_nodes_.push_back(new_node);
  }
  transplant(parent, extra_black, new_node, root);

  /*
   * new_node may point to nil, and this call sets the color to black (nil is
   * always black, so this is OK). however we treat nil as read-only, so we
   * only make this call that may throw a non-read-only assertion failure for
   * non-nil nodes.
   *
   * TODO: is there something fundmentally wrong with the algorithm that
   * new_node may even point to nil?
   */
  if (new_node != Node::Nil())
    new_node->set_red(false);
}

void TransactionImpl::serialize_intention(kvstore_proto::Intention& i,
    SharedNodeRef node, int& field_index, std::vector<SharedNodeRef>& delta)
{
  assert(node != nullptr);

  if (node == Node::Nil() || node->rid() != rid_)
    return;

  // serialize the left side of the tree. after the call returns,
  // maybe_left_offset will contain the offset of the last node that was
  // serialized. if the node is non-nil and is a new node in the afterimage,
  // then maybe_left_offset is valid (its validity is checked in
  // serialize_node_ptr).
  serialize_intention(i, node->left.ref(trace_), field_index, delta);
  auto maybe_left_offset = field_index - 1;

  serialize_intention(i, node->right.ref(trace_), field_index, delta);
  auto maybe_right_offset = field_index - 1;

  // new serialized node in the intention
  kvstore_proto::Node *dst = i.add_tree();
  serialize_node(dst, node, maybe_left_offset, maybe_right_offset);
  delta.push_back(node);
  field_index++;
}

void TransactionImpl::Put(const Slice& key, const Slice& value)
{
  assert(!committed_);
  assert(!aborted_);

  TraceApplier ta(this);

  /*
   * build copy of path to new node
   */
  std::deque<SharedNodeRef> path;

  auto base_root = root_ == nullptr ? src_root_.ref(trace_) : root_;
  auto root = insert_recursive(path, key, value, base_root);
  if (root == nullptr) {
    /*
     * this is the update case that is transformed into delete + put. an
     * optimization would be to 1) use the path constructed here to skip that
     * step in delete or 2) update the algorithm to handle this case
     * explicitly.
     */
    Delete(key); // first remove the key
    path.clear(); // new path will be built
    assert(root_ != nullptr); // delete set the root
    root = insert_recursive(path, key, value, root_);
    assert(root != nullptr); // a new root was added
  }

  path.push_back(Node::Nil());
  assert(path.size() >= 2);

  /*
   * balance the tree
   */
  auto nn = pop_front(path);
  auto parent = pop_front(path);

  while (parent->red()) {
    assert(!path.empty());
    auto grand_parent = path.front();
    if (grand_parent->left.ref(trace_) == parent)
      insert_balance(parent, nn, path, left, right, root);
    else
      insert_balance(parent, nn, path, right, left, root);
  }

  root->set_red(false);

  assert(root != nullptr);
  root_ = root;
}

void TransactionImpl::Delete(const Slice& key)
{
  assert(!committed_);
  assert(!aborted_);

  TraceApplier ta(this);

  std::deque<SharedNodeRef> path;

  auto base_root = root_ == nullptr ? src_root_.ref(trace_) : root_;
  auto root = delete_recursive(path, key, base_root);
  if (root == nullptr) {
    return;
  }

  //roots.push_back(node);
  path.push_back(Node::Nil());
  assert(path.size() >= 2);

  /*
   * remove and balance
   */
  auto removed = path.front();
  assert(removed != nullptr);
  assert(removed->key() == key);

  auto transplanted = removed->right.ref(trace_);
  assert(transplanted != nullptr);

  if (removed->left.ref(trace_) == Node::Nil()) {
    path.pop_front();
    transplant(path.front(), removed, transplanted, root);
    assert(transplanted != nullptr);
  } else if (removed->right.ref(trace_) == Node::Nil()) {
    path.pop_front();
    assert(removed->left.ref(trace_) != nullptr);
    transplanted = removed->left.ref(trace_);
    transplant(path.front(), removed, transplanted, root);
    assert(transplanted != nullptr);
  } else {
    assert(transplanted != nullptr);
    auto temp = removed;
    if (removed->right.ref(trace_)->rid() != rid_) {
      auto n = Node::Copy(removed->right.ref(trace_), db_, rid_);
      fresh_nodes_.push_back(n);
      removed->right.set_ref(n);
    }
    removed = build_min_path(removed->right.ref(trace_), path);
    transplanted = removed->right.ref(trace_);
    assert(transplanted != nullptr);

    //temp->key = std::move(removed->key);
    //temp->val = std::move(removed->val);
    temp->steal_payload(removed);

    transplant(path.front(), removed, transplanted, root);
    assert(transplanted != nullptr);
  }

  if (!removed->red())
    balance_delete(transplanted, path, root);

  assert(root != nullptr);
  root_ = root;
}

void TransactionImpl::Abort()
{
  assert(!committed_);
  assert(!aborted_);
  aborted_ = true;
  db_->AbortTransaction(this);
}

void TransactionImpl::Commit()
{
  assert(!committed_);
  assert(!aborted_);

  assert(trace_.empty());

  // nothing to do
  if (root_ == nullptr) {
    db_->AbortTransaction(this);
    committed_ = true;
    completed_ = true;
    return;
  }

  // after setting this to true, a spurious wake-up could cause the txn
  // finisher to start processing this transaction, so make sure we are ready
  // for that...
  committed_ = true;

  db_->CompleteTransaction(this);
  WaitComplete();
}

int TransactionImpl::Get(const Slice& key, std::string* val)
{
  assert(!committed_);
  assert(!aborted_);

  TraceApplier ta(this);

  auto cur = root_ == nullptr ? src_root_.ref(trace_) : root_;
  while (cur != Node::Nil()) {
    int cmp = key.compare(Slice(cur->key().data(),
          cur->key().size()));
    if (cmp == 0) {
      val->assign(cur->val().data(), cur->val().size());
      return 0;
    }
    cur = cmp < 0 ? cur->left.ref(trace_) :
      cur->right.ref(trace_);
  }
  return -ENOENT;
}

void TransactionImpl::SerializeAfterImage(kvstore_proto::Intention& i,
    std::vector<SharedNodeRef>& delta)
{
  assert(committed_);

  int field_index = 0;
  assert(root_ != nullptr);
  if (root_ == Node::Nil()) {
    // ???
  } else
    assert(root_->rid() == rid_);

  serialize_intention(i, root_, field_index, delta);
  i.set_snapshot(src_root_.csn());
}

void TransactionImpl::SetDeltaPosition(std::vector<SharedNodeRef>& delta,
    uint64_t pos)
{
  for (const auto nn : delta) {
    if (nn->left.ref_notrace()->rid() == rid_) {
      nn->left.set_csn(pos);
    }
    if (nn->right.ref_notrace()->rid() == rid_) {
      nn->right.set_csn(pos);
    }
  }

  // set the rid of these nodes to the log position where they are stored.
  for (auto nn : delta) {
    nn->set_rid(pos);
  }
}
