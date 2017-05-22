#ifndef ZLOG_INCLUDE_ZLOG_TRANSACTION_H
#define ZLOG_INCLUDE_ZLOG_TRANSACTION_H
#include <string>
#include <zlog/slice.h>

class Transaction {
 public:
  virtual ~Transaction() {}
  virtual void Put(const Slice& key, const Slice& value) = 0;
  virtual int Get(const Slice& key, std::string *value) = 0;
  virtual void Delete(const Slice& key) = 0;
  virtual void Commit() = 0;
  virtual void Abort() = 0;
};

#endif
