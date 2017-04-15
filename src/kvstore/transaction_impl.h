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

  void SerializeAfterImage(kvstore_proto::Intention& i,
      std::vector<SharedNodeRef>& delta);
  void SetDeltaPosition(std::vector<SharedNodeRef>& delta, uint64_t pos);

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
  SharedNodeRef root_;
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
  std::vector<SharedNodeRef> fresh_nodes_;

  static inline NodePtr& left(SharedNodeRef n) { return n->left; };
  static inline NodePtr& right(SharedNodeRef n) { return n->right; };

  std::vector<std::string> description_;

  static inline SharedNodeRef pop_front(std::deque<SharedNodeRef>& d) {
    auto front = d.front();
    d.pop_front();
    return front;
  }

  SharedNodeRef insert_recursive(std::deque<SharedNodeRef>& path,
      const Slice& key, const Slice& value, const SharedNodeRef& node);

  template<typename ChildA, typename ChildB>
  void insert_balance(SharedNodeRef& parent, SharedNodeRef& nn,
      std::deque<SharedNodeRef>& path, ChildA, ChildB, SharedNodeRef& root);

  template <typename ChildA, typename ChildB >
  SharedNodeRef rotate(SharedNodeRef parent, SharedNodeRef child,
      ChildA child_a, ChildB child_b, SharedNodeRef& root);

  SharedNodeRef delete_recursive(std::deque<SharedNodeRef>& path,
      const Slice& key, const SharedNodeRef& node);

  void transplant(SharedNodeRef parent, SharedNodeRef removed,
      SharedNodeRef transplanted, SharedNodeRef& root);

  SharedNodeRef build_min_path(SharedNodeRef node, std::deque<SharedNodeRef>& path);

  void balance_delete(SharedNodeRef extra_black,
      std::deque<SharedNodeRef>& path, SharedNodeRef& root);

  template<typename ChildA, typename ChildB>
  void mirror_remove_balance(SharedNodeRef& extra_black, SharedNodeRef& parent,
      std::deque<SharedNodeRef>& path, ChildA child_a, ChildB child_b,
      SharedNodeRef& root);

  // turn a transaction into a serialized protocol buffer
  void serialize_node_ptr(kvstore_proto::NodePtr *dst, NodePtr& src,
      const std::string& dir);
  void serialize_node(kvstore_proto::Node *dst, SharedNodeRef node,
      int field_index);
  void serialize_intention(kvstore_proto::Intention& i,
      SharedNodeRef node, int& field_index,
      std::vector<SharedNodeRef>& delta);
};

#endif
