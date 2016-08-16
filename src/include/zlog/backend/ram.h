#ifndef ZLOG_INCLUDE_ZLOG_RAM_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_RAM_BACKEND_H
#include <random>
#include <sstream>
#include <deque>
#include <map>
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

  virtual int AioAppend(const std::string& oid, uint64_t epoch,
      uint64_t position, const Slice& data, void *arg,
      std::function<void(void*, int)> callback)
  {
    assert(0);
  }

  virtual int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data, void *arg,
      std::function<void(void*, int)> callback)
  {
    assert(0);
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

class FakeSeqrClient : public zlog::SeqrClient {
 public:
  FakeSeqrClient() : SeqrClient("", "")
  {}

  void Connect() {}

  virtual int CheckTail(uint64_t epoch, const std::string& pool,
      const std::string& name, uint64_t *position, bool next)
  {
    entry *e;
    auto it = entries_.find(std::make_pair(pool, name));
    if (it == entries_.end()) {
      e = &entries_[std::make_pair(pool, name)];
      e->seq = 0;
    } else
      e = &it->second;
    
    if (next) {
      uint64_t tail = e->seq.fetch_add(1); // returns previous value
      *position = tail;
    } else
      *position = e->seq.load();

    return 0;
  }

  virtual int CheckTail(uint64_t epoch, const std::string& pool,
      const std::string& name, std::vector<uint64_t>& positions, size_t count)
  {
    assert(0);
  }

  virtual int CheckTail(uint64_t epoch, const std::string& pool,
      const std::string& name, const std::set<uint64_t>& stream_ids,
      std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
      uint64_t *position, bool next)
  {
    if (stream_ids.size() == 0)
      return -EINVAL;

    entry *e;
    auto it = entries_.find(std::make_pair(pool, name));
    if (it == entries_.end()) {
      e = &entries_[std::make_pair(pool, name)];
      e->seq = 0;
    } else
      e = &it->second;

    if (next) {
      std::map<uint64_t, std::vector<uint64_t>> result;

      // make a copy of the current backpointers
      for (std::set<uint64_t>::const_iterator it = stream_ids.begin();
          it != stream_ids.end(); it++) {

        uint64_t stream_id = *it;
        stream_index_t::const_iterator stream_it = e->streams.find(stream_id);
        if (stream_it == e->streams.end()) {
          /*
           * If a stream doesn't exist initialize an empty set of backpointers.
           * How do we know a stream doesn't exist? During log initialization we
           * setup all existing logs...
           */
          e->streams[stream_id] = stream_backpointers_t();

          std::vector<uint64_t> ptrs;
          result[stream_id] = ptrs;
          continue;
        }

        std::vector<uint64_t> ptrs(stream_it->second.begin(),
            stream_it->second.end());
        result[stream_id] = ptrs;
      }

      uint64_t next_pos = e->seq.fetch_add(1);

      // add new position to each stream
      for (std::set<uint64_t>::const_iterator it = stream_ids.begin();
          it != stream_ids.end(); it++) {
        uint64_t stream_id = *it;
        stream_backpointers_t& backpointers = e->streams.at(stream_id);
        backpointers.push_back(next_pos);
        if (backpointers.size() > 10)
          backpointers.pop_front();
      }

      if (position)
        *position = next_pos;
      stream_backpointers.swap(result);

      return 0;
    } else {
      std::map<uint64_t, std::vector<uint64_t>> result;

      // make a copy of the current backpointers
      for (std::set<uint64_t>::const_iterator it = stream_ids.begin();
          it != stream_ids.end(); it++) {

        uint64_t stream_id = *it;
        stream_index_t::const_iterator stream_it = e->streams.find(stream_id);
        if (stream_it == e->streams.end()) {
          /*
           * If a stream doesn't exist initialize an empty set of backpointers.
           * How do we know a stream doesn't exist? During log initialization we
           * setup all existing logs...
           */
          e->streams[stream_id] = stream_backpointers_t();

          std::vector<uint64_t> ptrs;
          result[stream_id] = ptrs;
          continue;
        }

        std::vector<uint64_t> ptrs(stream_it->second.begin(),
            stream_it->second.end());
        result[stream_id] = ptrs;
      }

      if (position)
        *position = e->seq.load();
      stream_backpointers.swap(result);

      return 0;
    }
  }

 private:
  typedef std::deque<uint64_t> stream_backpointers_t;
  typedef std::map<uint64_t, stream_backpointers_t> stream_index_t;

  struct entry {
    std::atomic<uint64_t> seq;
    stream_index_t streams;
  };

  std::map<std::pair<std::string, std::string>, entry> entries_;
};


#endif
