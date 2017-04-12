#ifndef ZLOG_KVSTORE_TRANSACTION_H
#define ZLOG_KVSTORE_TRANSACTION_H
#include <deque>
#include "node.h"
#include "kvstore/kvstore.pb.h"
#include "zlog/transaction.h"

class DBImpl;

/*
 * would be nice to have some mechanism here for really enforcing the idea
 * that this transaction is isolated.
 */
class TransactionImpl : public Transaction {
 public:
  TransactionImpl(DBImpl *db, NodePtr root, uint64_t snapshot, uint64_t rid) :
    db_(db), src_root_(root), snapshot_(snapshot), root_(nullptr), rid_(rid),
    committed_(false),
    completed_(false)
  {
    // TODO: reserve trace as average height
  }

  virtual void Put(const Slice& key, const Slice& value) override;
  virtual void Delete(const Slice& key) override;
  virtual int Get(const Slice& key, std::string *value) override;
  virtual void Commit() override;

 public:
  bool Committed() const {
    return committed_;
  }

  bool Completed() const {
    return completed_;
  }

  void MarkComplete() {
    lock_.lock();
    completed_ = true;
    lock_.unlock();
    completed_cond_.notify_one();
  }

  void SerializeAfterImage(std::string *blob);

 private:
  class TraceApplier {
   public:
    explicit TraceApplier(TransactionImpl *txn) :
      txn_(txn)
    {}

    ~TraceApplier() {
      txn_->UpdateLRU();
    }

   private:
    TransactionImpl *txn_;
  };

  DBImpl *db_;

  // database snapshot
  NodePtr src_root_;
  const uint64_t snapshot_;

  // transaction after image
  NodeRef root_;
  const uint64_t rid_;

  std::mutex lock_;

  /*
   * committed_: when the client calls Commit
   * completed_: when its safe to ack the client
   */
  bool committed_;
  bool completed_;

  std::condition_variable completed_cond_;

  void WaitComplete() {
    std::unique_lock<std::mutex> lk(lock_);
    completed_cond_.wait(lk, [this]{ return completed_; });
  }

  // access trace used to update lru cache. the trace is applied and reset
  // after each operation (e.g. get/put/etc) or if the transaction accesses
  // the cache to resolve a pointer (e.g. accessing the log).
  std::vector<std::pair<int64_t, int>> trace_;
  void UpdateLRU();

  // keep new nodes alive for the duration of the transaction until we
  // construct the intention. this is needed because NodePtr contains weak_ptr
  // so new NodeRef nodes (see: insert_recursive) just disappear, and we can't
  // let that happen because we don't store them in the the log or any other
  // type of cache. future options:
  //
  //   1. use a SharedNodePtr type in transactions
  //   2. probably better: integrate some sort of cache so that we can support
  //   transactions that are really large
  //
  std::vector<NodeRef> fresh_nodes_;

  static inline NodePtr& left(NodeRef n) { return n->left; };
  static inline NodePtr& right(NodeRef n) { return n->right; };

  std::vector<std::string> description_;

  static inline NodeRef pop_front(std::deque<NodeRef>& d) {
    auto front = d.front();
    d.pop_front();
    return front;
  }

  NodeRef insert_recursive(std::deque<NodeRef>& path,
      const Slice& key, const Slice& value, const NodeRef& node);

  template<typename ChildA, typename ChildB>
  void insert_balance(NodeRef& parent, NodeRef& nn,
      std::deque<NodeRef>& path, ChildA, ChildB, NodeRef& root);

  template <typename ChildA, typename ChildB >
  NodeRef rotate(NodeRef parent, NodeRef child,
      ChildA child_a, ChildB child_b, NodeRef& root);

  NodeRef delete_recursive(std::deque<NodeRef>& path,
      const Slice& key, const NodeRef& node);

  void transplant(NodeRef parent, NodeRef removed,
      NodeRef transplanted, NodeRef& root);

  NodeRef build_min_path(NodeRef node, std::deque<NodeRef>& path);

  void balance_delete(NodeRef extra_black,
      std::deque<NodeRef>& path, NodeRef& root);

  template<typename ChildA, typename ChildB>
  void mirror_remove_balance(NodeRef& extra_black, NodeRef& parent,
      std::deque<NodeRef>& path, ChildA child_a, ChildB child_b,
      NodeRef& root);

  // turn a transaction into a serialized protocol buffer
  void serialize_node_ptr(kvstore_proto::NodePtr *dst, NodePtr& src,
      const std::string& dir);
  void serialize_node(kvstore_proto::Node *dst, NodeRef node,
      int field_index);
  void serialize_intention(kvstore_proto::Intention& i,
      NodeRef node, int& field_index);

  void set_intention_self_csn_recursive(uint64_t rid, NodeRef node,
      uint64_t pos);

  void set_intention_self_csn(NodeRef root, uint64_t pos);
};

#endif
