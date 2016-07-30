#ifndef ZLOG_KVSTORE_ITERATOR_H
#define ZLOG_KVSTORE_ITERATOR_H
// interface derived from facebook/rocksdb/iterator
#include <stack>
#include "node.h"
#include "snapshot.h"

class Iterator {
 public:
  Iterator(Snapshot snapshot);

  // An iterator is either positioned at a key/value pair, or
  // not valid.  This method returns true iff the iterator is valid.
  bool Valid() const;

  // Position at the first key in the source.  The iterator is Valid()
  // after this call iff the source is not empty.
  void SeekToFirst();

  // Position at the last key in the source.  The iterator is
  // Valid() after this call iff the source is not empty.
  void SeekToLast();

  // Position at the first key in the source that at or past target
  // The iterator is Valid() after this call iff the source contains
  // an entry that comes at or past target.
  void Seek(const std::string& target);

  // Moves to the next entry in the source.  After this call, Valid() is
  // true iff the iterator was not positioned at the last entry in the source.
  // REQUIRES: Valid()
  void Next();

  // Moves to the previous entry in the source.  After this call, Valid() is
  // true iff the iterator was not positioned at the first entry in source.
  // REQUIRES: Valid()
  void Prev();

  // Return the key for the current entry.  The underlying storage for
  // the returned slice is valid only until the next modification of
  // the iterator.
  // REQUIRES: Valid()
  std::string key() const;

  // Return the value for the current entry.  The underlying storage for
  // the returned slice is valid only until the next modification of
  // the iterator.
  // REQUIRES: !AtEnd() && !AtStart()
  std::string value() const;

  // If an error has occurred, return it.  Else return an ok status.
  // If non-blocking IO is requested and this operation cannot be
  // satisfied without doing some IO, then this returns Status::Incomplete().
  int status() const;

#if 0
  // Property "rocksdb.iterator.is-key-pinned":
  //   If returning "1", this means that the Slice returned by key() is valid
  //   as long as the iterator is not deleted.
  //   It is guaranteed to always return "1" if
  //      - Iterator created with ReadOptions::pin_data = true
  //      - DB tables were created with
  //        BlockBasedTableOptions::use_delta_encoding = false.
  // Property "rocksdb.iterator.super-version-number":
  //   LSM version used by the iterator. The same format as DB Property
  //   kCurrentSuperVersionNumber. See its comment for more information.
  Status GetProperty(std::string prop_name, std::string* prop);
#endif

 private:
  // No copying allowed
  //Iterator(const Iterator&);
  //void operator=(const Iterator&);

  std::stack<NodeRef> stack_;
  NodeRef curr_;
  Snapshot snapshot_;
};

#endif
