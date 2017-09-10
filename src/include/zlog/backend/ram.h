#ifndef ZLOG_INCLUDE_ZLOG_RAM_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_RAM_BACKEND_H
#include <random>
#include <sstream>
#include <map>
#include <unordered_map>

class RAMBackend : public Backend {
 public:
  RAMBackend() {
    std::stringstream ss;
    ss << "fakepool." << std::rand();
    pool_ = ss.str();
  }

  int CreateLog(const std::string& name,
      const std::string& initial_view) override {
    assert(0);
  }

  virtual int OpenLog(const std::string& name,
      std::string& hoid, std::string& prefix) {
    assert(0);
  }

  int ProposeView(const std::string& hoid,
      uint64_t epoch, const std::string& view) {
    assert(0);
  }

  int ReadViews(const std::string& hoid, uint64_t epoch,
      std::map<uint64_t, std::string>& views) override {
    assert(0);
  }

  virtual std::string pool() {
    return pool_;
  }

  virtual int Exists(const std::string& oid) {
    std::lock_guard<std::mutex> l(lock_);
    auto it = db_.find(oid);
    if (it == db_.end())
      return -ENOENT;
    return 0;
  }

#if 0
  virtual int CreateHeadObject(const std::string& oid,
      const zlog_proto::MetaLog& data) {
    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);
    if (it != db_.end())
      return -EEXIST;

    // projection blob
    assert(data.IsInitialized());
    std::string blob;
    assert(data.SerializeToString(&blob));

    object obj;
    obj.projections[0] = blob;
    db_[oid] = obj;

    return 0;
  }

  virtual int SetProjection(const std::string& oid, uint64_t epoch,
      const zlog_proto::MetaLog& data) {
    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);
    if (it == db_.end())
      return -ENOENT;

    auto latest = it->second.projections.rbegin();
    if (latest == it->second.projections.rend() && epoch != 0)
      return -EINVAL;

    if (latest != it->second.projections.rend() && epoch != (latest->first + 1))
      return -EINVAL;

    auto it2 = it->second.projections.find(epoch);
    if (it2 != it->second.projections.end())
      return -EINVAL;

    assert(data.IsInitialized());
    std::string blob;
    assert(data.SerializeToString(&blob));

    it->second.projections[epoch] = blob;

    return 0;
  }

  virtual int LatestProjection(const std::string& oid,
      uint64_t *epoch, zlog_proto::MetaLog& config) {
    std::lock_guard<std::mutex> l(lock_);
    auto it = db_.find(oid);
    if (it == db_.end())
      return -ENOENT;
    auto it2 = it->second.projections.rbegin();
    if (it2 == it->second.projections.rend())
      return -ENOENT;
    assert(config.ParseFromString(it2->second));
    *epoch = it2->first;
    return 0;
  }
#endif

  virtual int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos, bool *empty) {
    assert(0);
    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);
    if (it == db_.end() || !it->second.sealed)
      return -ENOENT;

    if (epoch != it->second.epoch)
      return -EINVAL;

    if (it->second.entries.empty())
      *pos = 0;
    else
      *pos = it->second.entries.rbegin()->first + 1;

    return 0;
  }

  virtual int Seal(const std::string& oid, uint64_t epoch) {
    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);
    if (it != db_.end() && it->second.sealed) {
      if (epoch <= it->second.epoch)
        return -ESPIPE;
    }

    // object reference
    object *obj;
    if (it == db_.end())
      obj = &db_[oid];
    else
      obj = &it->second;

    obj->epoch = epoch;
    obj->sealed = true;

    return 0;
  }

  virtual int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position) {

    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);

    // check epoch
    int ret = CheckEpoch(epoch, it);
    if (ret)
      return ret;

    // object reference
    object *obj;
    if (it == db_.end())
      obj = &db_[oid];
    else
      obj = &it->second;

    // check entry
    auto entry_it = obj->entries.find(position);
    if (entry_it == obj->entries.end()) {
      log_entry e;
      e.trimmed = false;
      e.invalidated = false;
      e.data.assign(data.data(), data.size());
      obj->entries[position] = e;
      return 0;
    }

    return -EROFS;
  }

  virtual int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data) {

    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);

    // check epoch
    int ret = CheckEpoch(epoch, it);
    if (ret)
      return ret;

    // object reference
    object *obj;
    if (it == db_.end())
      obj = &db_[oid];
    else
      obj = &it->second;

    // check entry
    auto entry_it = obj->entries.find(position);
    if (entry_it == obj->entries.end())
      return -ENOENT;

    if (entry_it->second.trimmed || entry_it->second.invalidated)
      return -ENODATA;

    *data = entry_it->second.data;

    return 0;
  }

  virtual int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position) {

    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);

    // check epoch
    int ret = CheckEpoch(epoch, it);
    if (ret)
      return ret;

    // object reference
    object *obj;
    if (it == db_.end())
      obj = &db_[oid];
    else
      obj = &it->second;

    // check entry
    auto entry_it = obj->entries.find(position);
    if (entry_it == obj->entries.end()) {
      log_entry e;
      e.trimmed = true;
      obj->entries[position] = e;
      return 0;
    } else {
      if (entry_it->second.trimmed)
        return 0;
      entry_it->second.trimmed = true;
      entry_it->second.data.clear();
      return 0;
    }
  }

  virtual int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position) {

    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);

    // check epoch
    int ret = CheckEpoch(epoch, it);
    if (ret)
      return ret;

    // object reference
    object *obj;
    if (it == db_.end())
      obj = &db_[oid];
    else
      obj = &it->second;

    // check entry
    auto entry_it = obj->entries.find(position);
    if (entry_it == obj->entries.end()) {
      log_entry e;
      e.trimmed = true;
      e.invalidated = true;
      obj->entries[position] = e;
      return 0;
    } else {
      if (entry_it->second.trimmed ||
          entry_it->second.invalidated) {
        return 0;
      }
      return -EROFS;
    }
  }

  virtual int AioWrite(const std::string& oid, uint64_t epoch,
      uint64_t position, const Slice& data, void *arg,
      std::function<void(void*, int)> callback)
  {
    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);

    // check epoch
    int ret = CheckEpoch(epoch, it);
    if (ret) {
      callback(arg, ret);
      return 0;
    }

    // object reference
    object *obj;
    if (it == db_.end())
      obj = &db_[oid];
    else
      obj = &it->second;

    // check entry
    auto entry_it = obj->entries.find(position);
    if (entry_it == obj->entries.end()) {
      log_entry e;
      e.trimmed = false;
      e.invalidated = false;
      e.data.assign(data.data(), data.size());
      obj->entries[position] = e;
      callback(arg, 0);
      return 0;
    }

    callback(arg, -EROFS);
    return 0;
  }

  virtual int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data, void *arg,
      std::function<void(void*, int)> callback)
  {
    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);

    // check epoch
    int ret = CheckEpoch(epoch, it);
    if (ret) {
      callback(arg, ret);
      return 0;
    }

    // object reference
    object *obj;
    if (it == db_.end())
      obj = &db_[oid];
    else
      obj = &it->second;

    // check entry
    auto entry_it = obj->entries.find(position);
    if (entry_it == obj->entries.end()) {
      callback(arg, -ENOENT);
      return 0;
    }

    if (entry_it->second.trimmed || entry_it->second.invalidated) {
      callback(arg, -ENODATA);
      return 0;
    }

    *data = entry_it->second.data;

    callback(arg, 0);
    return 0;
  }

 private:
  struct log_entry {
    bool trimmed;
    bool invalidated;
    std::string data;
  };

  struct object {
    bool sealed;
    uint64_t epoch;
    std::map<uint64_t, std::string> projections;
    std::map<uint64_t, log_entry> entries;
  };

  int CheckEpoch(uint64_t epoch,
      std::unordered_map<std::string, object>::iterator& it) {
    if (it == db_.end())
      return 0;
    if (it->second.sealed && epoch <= it->second.epoch)
      return -ESPIPE;
    return 0;
  }

  std::mutex lock_;
  std::string pool_;
  std::unordered_map<std::string, object> db_;
};
#endif
