#pragma once
#include <vector>
#include <sstream>
#include <iostream>
#include <memory>
#include <lmdb.h>
#include "zlog/backend.h"

namespace zlog {
namespace storage {
namespace lmdb {

class LMDBBackend : public Backend {
 public:
  LMDBBackend() {
    options["scheme"] = "lmdb";
  }

  ~LMDBBackend();

  void Init(const std::string& path);

  int Initialize(const std::map<std::string, std::string>& opts) override;

  void Close();

  std::map<std::string, std::string> meta() override;

  int CreateLog(const std::string& name,
      const std::string& initial_view) override;

  int OpenLog(const std::string& name,
      std::string& hoid, std::string& prefix) override;

  int ReadViews(const std::string& hoid, uint64_t epoch,
      std::map<uint64_t, std::string>& views) override;

  int ProposeView(const std::string& hoid,
      uint64_t epoch, const std::string& view) override;

  int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      std::string *data) override;

  int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position, uint32_t stride,
      uint32_t max_size) override;

  int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size) override;

  int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size) override;

  int Seal(const std::string& oid,
      uint64_t epoch) override;

  int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos, bool *empty) override;

  int AioWrite(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      const Slice& data, void *arg,
      std::function<void(void*, int)> callback) override;

  int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      std::string *data, void *arg,
      std::function<void(void*, int)> callback) override;

 private:
  std::map<std::string, std::string> options;
  MDB_env *env;
  MDB_dbi db_obj;

  struct ProjectionObject {
    ProjectionObject() : latest_epoch(0) {}
    uint64_t latest_epoch;
  };

  struct LogObject {
    uint64_t epoch;
    LogObject() : epoch(0) {}
  };

  struct LogMaxPos {
    uint64_t maxpos;
  };

  struct LogEntry {
    bool trimmed;
    bool invalidated;
    LogEntry() : trimmed(false), invalidated(false) {}
  };

  struct Transaction {
    MDB_txn *txn;
    LMDBBackend *be;
    bool closed;

    Transaction(MDB_txn *txn, LMDBBackend *be) :
      txn(txn), be(be), closed(false)
    {}

    ~Transaction() {
      if (!closed) {
        Abort();
        assert(0);
      }
    }

    void Abort() {
      mdb_txn_abort(txn);
      closed = true;
    }

    int Commit() {
      closed = true;
      return mdb_txn_commit(txn);
    }

    int Get(const std::string& key, MDB_val& val) {
      MDB_val k;
      k.mv_size = key.size();
      k.mv_data = (void*)key.data();
      int ret = mdb_get(txn, be->db_obj, &k, &val);
      assert(ret == 0 || ret == MDB_NOTFOUND);
      if (ret == MDB_NOTFOUND)
        return -ENOENT;
      return 0;
    }

    int Put(const std::string& key, MDB_val& val, bool exclusive) {
      MDB_val k;
      k.mv_size = key.size();
      k.mv_data = (void*)key.data();
      int flags = exclusive ? MDB_NOOVERWRITE : 0;
      int ret = mdb_put(txn, be->db_obj, &k, &val, flags);
      assert(ret == 0 || ret == MDB_KEYEXIST);
      if (ret == MDB_KEYEXIST)
        return -EEXIST;
      return 0;
    }

    int Put(const std::string& key, const std::vector<unsigned char>& val,
        bool exclusive) {
      MDB_val v;
      v.mv_size = val.size();
      v.mv_data = (void*)val.data();
      return Put(key, v, exclusive);
    }
  };

  Transaction NewTransaction(bool read_only = false);

  std::string LogEntryKey(const std::string& oid,
      uint64_t position)
  {
    std::stringstream ss;
    ss << oid << "." << position;
    return ss.str();
  }

  std::string MaxPosKey(const std::string& oid)
  {
    std::stringstream ss;
    ss << oid << ".maxpos";
    return ss.str();
  }

  std::string ObjectKey(const std::string& oid)
  {
    std::stringstream ss;
    ss << oid;
    return ss.str();
  }

  std::string ProjectionKey(const std::string& oid, uint64_t epoch)
  {
    std::stringstream ss;
    ss << oid << "." << epoch;
    return ss.str();
  }

  int CheckEpoch(Transaction& txn, uint64_t epoch, const std::string& oid,
      bool eq = false);

 private:
  bool closed = false;
};

}
}
}
