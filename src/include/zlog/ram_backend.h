#ifndef ZLOG_INCLUDE_ZLOG_RAM_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_RAM_BACKEND_H
#include <random>
#include <sstream>
#include <unordered_map>

class RAMBackend : public Backend {
 public:
  RAMBackend() : Backend(NULL) {
    std::srand(time(NULL));
    std::stringstream ss;
    ss << "fakepool." << std::rand();
    pool_ = ss.str();

    pool_ = "rbd";
  }

  virtual std::string pool() {
    return pool_;
  }

  virtual int Exists(const std::string& oid) {
    std::lock_guard<std::mutex> l(lock_);
    auto it = db_.find(oid);
    if (it == db_.end())
      return -ENOENT;
    return ZLOG_OK;
  }

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

    return ZLOG_OK;
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

    return ZLOG_OK;
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
    return ZLOG_OK;
  }

  virtual int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos) {
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

    return Backend::ZLOG_OK;
  }

  virtual int Seal(const std::string& oid, uint64_t epoch) {
    std::lock_guard<std::mutex> l(lock_);

    auto it = db_.find(oid);
    if (it != db_.end() && it->second.sealed) {
      if (epoch <= it->second.epoch)
        return Backend::ZLOG_INVALID_EPOCH;
    }

    // object reference
    object *obj;
    if (it == db_.end())
      obj = &db_[oid];
    else
      obj = &it->second;

    obj->epoch = epoch;
    obj->sealed = true;

    return Backend::ZLOG_OK;
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
      return Backend::ZLOG_OK;
    }

    return Backend::ZLOG_READ_ONLY;
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
      return Backend::ZLOG_NOT_WRITTEN;

    if (entry_it->second.trimmed || entry_it->second.invalidated)
      return Backend::ZLOG_INVALIDATED;

    *data = entry_it->second.data;

    return Backend::ZLOG_OK;
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
      return Backend::ZLOG_OK;
    } else {
      if (entry_it->second.trimmed)
        return Backend::ZLOG_OK;
      entry_it->second.trimmed = true;
      entry_it->second.data.clear();
      return Backend::ZLOG_OK;
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
      return Backend::ZLOG_OK;
    } else {
      if (entry_it->second.trimmed ||
          entry_it->second.invalidated) {
        return Backend::ZLOG_OK;
      }
      return Backend::ZLOG_READ_ONLY;
    }
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
      return Backend::ZLOG_STALE_EPOCH;
    return 0;
  }

  std::mutex lock_;
  std::string pool_;
  std::unordered_map<std::string, object> db_;
};

#endif
