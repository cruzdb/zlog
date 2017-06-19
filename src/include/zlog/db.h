#ifndef ZLOG_INCLUDE_ZLOG_DB_H
#define ZLOG_INCLUDE_ZLOG_DB_H
#include <vector>
#include "zlog/log.h"
#include "zlog/transaction.h"
#include "zlog/iterator.h"

class Snapshot;

class DB {
 public:
  DB() {}
  virtual ~DB();

  DB(const DB&) = delete;
  void operator=(const DB&) = delete;

  /*
   *
   */
  static int Open(zlog::Log *log, bool create_if_empty, DB **db);

  /*
   *
   */
  virtual Transaction *BeginTransaction() = 0;

  /*
   *
   */
  virtual Snapshot *GetSnapshot() = 0;

  /*
   *
   */
  virtual void ReleaseSnapshot(Snapshot *snapshot) = 0;

  /*
   *
   */
  virtual Iterator *NewIterator(Snapshot *snapshot) = 0;

  Iterator *NewIterator() {
    return NewIterator(GetSnapshot());
  }

  /*
   * Lookup a key in the latest committed database snapshot.
   */
  virtual int Get(const Slice& key, std::string *value) = 0;

  /*
   *
   */
  virtual void write_dot_history(std::ostream& out,
      std::vector<Snapshot*>& snapshots) = 0;
  virtual void validate() = 0;
};

#endif
