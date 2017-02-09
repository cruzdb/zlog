#ifndef ZLOG_INCLUDE_ZLOG_TRANSACTION_H
#define ZLOG_INCLUDE_ZLOG_TRANSACTION_H

class Transaction {
 public:
  virtual void Put(const std::string& key, const std::string& val) = 0;
  virtual void Delete(std::string key) = 0;
  virtual void Commit() = 0;
  virtual int Get(const std::string& key, std::string* val) = 0;
};

#endif
