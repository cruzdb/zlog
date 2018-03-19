#include <algorithm>
#include <cmath>
#include <vector>
#include "storage/ram/cruzdb.pb.h"
#include "zlog/backend.h"
#include "zlog/backend/ram.h"

namespace zlog {
namespace storage {
namespace ram {

RAMBackend::~RAMBackend()
{
}

int RAMBackend::Initialize(
    const std::map<std::string, std::string>& opts)
{
  return 0;
}

std::map<std::string, std::string> RAMBackend::meta()
{
  return options_;
}

int RAMBackend::CreateLog(const std::string& name,
    const std::string& initial_view)
{
  std::lock_guard<std::mutex> lk(lock_);

  ProjectionObject proj_obj;
  proj_obj.projections.emplace(proj_obj.latest_epoch, initial_view);
  auto ret = objects_.emplace(name, proj_obj);
  if (!ret.second) {
    return -EEXIST;
  }

  return 0;
}

int RAMBackend::OpenLog(const std::string& name,
    std::string& hoid, std::string& prefix)
{
  std::lock_guard<std::mutex> lk(lock_);

  auto it = objects_.find(name);
  if (it == objects_.end()) {
    return -ENOENT;
  }

  hoid = name;
  prefix = name;

  return 0;
}

int RAMBackend::ReadViews(const std::string& hoid, uint64_t epoch,
    std::map<uint64_t, std::string>& views)
{
  std::lock_guard<std::mutex> lk(lock_);

  auto it = objects_.find(hoid);
  if (it == objects_.end()) {
    return -ENOENT;
  }

  auto& proj_obj = boost::get<ProjectionObject>(it->second);
  if (epoch > proj_obj.latest_epoch) {
    return 0;
  }

  auto it2 = proj_obj.projections.find(epoch);
  if (it2 == proj_obj.projections.end())
    return -ENOENT;

  views.emplace(epoch, it2->second);

  return 0;
}

int RAMBackend::ProposeView(const std::string& hoid,
    uint64_t epoch, const std::string& view)
{
  std::lock_guard<std::mutex> lk(lock_);

  auto it = objects_.find(hoid);
  if (it == objects_.end()) {
    assert(epoch == 0);
  }

  ProjectionObject& proj_obj = boost::get<ProjectionObject>(it->second);
  assert(epoch == (proj_obj.latest_epoch + 1));

  auto ret = proj_obj.projections.emplace(epoch, view);
  if (!ret.second) {
    return -EEXIST;
  }

  proj_obj.latest_epoch = epoch;

  return 0;
}

int RAMBackend::Read(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, false, lobj);
  if (ret) {
    return ret;
  }

  if (lobj) {
    const auto it = lobj->entries.find(position);
    if (it == lobj->entries.end())
      return -ENOENT;

    const LogEntry& entry = it->second;
    if (entry.trimmed || entry.invalidated)
      return -ENODATA;

    data->assign(entry.data);
    return 0;
  } else {
    return -ENOENT;
  }
}

int RAMBackend::Read(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data,
    std::map<int, std::string> *vals)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, false, lobj);
  if (ret) {
    return ret;
  }

  if (lobj) {
    const auto it = lobj->entries.find(position);
    if (it == lobj->entries.end())
      return -ENOENT;

    const LogEntry& entry = it->second;
    if (entry.trimmed || entry.invalidated)
      return -ENODATA;

    if (data)
      data->assign(entry.data);

    *vals = entry.items;
    return 0;
  } else {
    return -ENOENT;
  }
}

// TODO: all three versions of Read can be unified
int RAMBackend::Read(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data, const std::set<int>& keys,
    std::map<int, std::string> *vals)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, false, lobj);
  if (ret) {
    return ret;
  }

  if (lobj) {
    const auto it = lobj->entries.find(position);
    if (it == lobj->entries.end())
      return -ENOENT;

    const LogEntry& entry = it->second;
    if (entry.trimmed || entry.invalidated)
      return -ENODATA;

    if (data)
      data->assign(entry.data);

    std::map<int, std::string> vals_out;
    for (auto key : keys) {
      auto it = entry.items.find(key);
      if (it != entry.items.end())
        vals_out.emplace(it->first, it->second);
    }
    vals->swap(vals_out);

    return 0;
  } else {
    return -ENOENT;
  }
}

// TODO: all three versions of Read can be unified
int RAMBackend::Read(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data, const std::set<int>& keys,
    float f, std::map<int, std::string> *vals)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, false, lobj);
  if (ret) {
    return ret;
  }

  if (lobj) {
    const auto it = lobj->entries.find(position);
    if (it == lobj->entries.end())
      return -ENOENT;

    const LogEntry& entry = it->second;
    if (entry.trimmed || entry.invalidated)
      return -ENODATA;

    if (data)
      data->assign(entry.data);

    // i guess we could probably create something even more inefficient...
    std::vector<std::pair<int, std::string>> kvs;
    for (auto e : entry.items) {
      kvs.push_back(e);
    }
    std::random_shuffle(kvs.begin(), kvs.end());

    int count = std::ceil(f * kvs.size());
    count = std::max(0, count);
    count = std::min(count, (int)kvs.size());
    assert(count >= 0 && count <= (int)kvs.size());

    std::map<int, std::string> vals_out;
    for (int i = 0; i < count; i++) {
      vals_out.emplace(kvs[i].first, kvs[i].second);
    }

    for (auto key : keys) {
      if (vals_out.find(key) == vals_out.end()) {
        auto it = entry.items.find(key);
        if (it != entry.items.end()) {
          vals_out.emplace(it->first, it->second);
        }
      }
    }
    vals->swap(vals_out);

    return 0;
  } else {
    return -ENOENT;
  }
}

int RAMBackend::Read(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data, const Slice *key_target,
    const std::set<int>& keys, std::map<int, std::string> *vals)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, false, lobj);
  if (ret) {
    return ret;
  }

  if (lobj) {
    const auto it = lobj->entries.find(position);
    if (it == lobj->entries.end())
      return -ENOENT;

    const LogEntry& entry = it->second;
    if (entry.trimmed || entry.invalidated)
      return -ENODATA;

    if (data)
      data->assign(entry.data);

    // starting node. we can generalize the semantics of the keys parameter
    // later.
    assert(keys.size() == 1);
    int offset = *keys.begin();

    std::map<int, std::string> vals_out;
    while (true) {
      auto blob = entry.items.at(offset);
      vals_out.emplace(offset, blob);

      // break immediately once the requested key offset is added to the output.
      // otherwise we'll try to traverse down a path.
      if (!key_target) {
        break;
      }

      cruzdb_proto::Node node;
      assert(node.ParseFromString(blob));
      assert(node.IsInitialized());

      int cmp = key_target->compare(Slice(node.key().data(),
            node.key().size()));
      if (cmp == 0)
        break;
      else if (cmp < 0) {
        if (node.left().self()) {
          assert(!node.left().nil());
          offset = node.left().off();
        } else {
          break;
        }
      } else {
        assert(cmp > 0);
        if (node.right().self()) {
          assert(!node.right().nil());
          offset = node.right().off();
        } else {
          break;
        }
      }
    }
    vals->swap(vals_out);
    return 0;
  } else {
    return -ENOENT;
  }
}

int RAMBackend::Write(const std::string& oid, const Slice& data,
    uint64_t epoch, uint64_t position)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, false, lobj);
  if (ret) {
    return ret;
  }

  if (!lobj) {
    auto ret = objects_.emplace(oid, LogObject());
    lobj = &boost::get<LogObject>(ret.first->second);
  }

  auto it = lobj->entries.find(position);
  if (it == lobj->entries.end()) {
    // TODO: more efficent!
    LogEntry entry;
    entry.data = data.ToString();
    lobj->entries.emplace(position, entry);
    lobj->maxpos = std::max(lobj->maxpos, position);
    return 0;
  } else {
    return -EROFS;
  }
}

// TODO: unify with the other Write interface
int RAMBackend::Write(const std::string& oid, const Slice& data,
    const std::map<int, std::string>& entries,
    uint64_t epoch, uint64_t position)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, false, lobj);
  if (ret) {
    return ret;
  }

  if (!lobj) {
    auto ret = objects_.emplace(oid, LogObject());
    lobj = &boost::get<LogObject>(ret.first->second);
  }

  auto it = lobj->entries.find(position);
  if (it == lobj->entries.end()) {
    std::map<int, std::string> items;
    for (auto& it : entries) {
      items.emplace(it.first, it.second);
    }
    LogEntry entry;
    entry.items = items;
    entry.data = data.ToString();
    lobj->entries.emplace(position, entry);
    lobj->maxpos = std::max(lobj->maxpos, position);
    return 0;
  } else {
    return -EROFS;
  }
}

int RAMBackend::Trim(const std::string& oid, uint64_t epoch,
    uint64_t position)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, false, lobj);
  if (ret) {
    return ret;
  }

  if (!lobj) {
    auto ret = objects_.emplace(oid, LogObject());
    lobj = &boost::get<LogObject>(ret.first->second);
  }

  auto it = lobj->entries.find(position);
  if (it == lobj->entries.end()) {
    LogEntry entry;
    entry.trimmed = true;
    entry.invalidated = true;
    lobj->entries.emplace(position, entry);
  } else {
    auto& entry = it->second;
    entry.trimmed = true;
    entry.data.clear();
  }

  return 0;
}

int RAMBackend::Fill(const std::string& oid, uint64_t epoch,
    uint64_t position)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, false, lobj);
  if (ret) {
    return ret;
  }

  if (!lobj) {
    auto ret = objects_.emplace(oid, LogObject());
    lobj = &boost::get<LogObject>(ret.first->second);
  }

  auto it = lobj->entries.find(position);
  if (it == lobj->entries.end()) {
    LogEntry entry;
    entry.trimmed = true;
    entry.invalidated = true;
    lobj->entries.emplace(position, entry);
    return 0;
  } else {
    auto& entry = it->second;
    if (entry.trimmed || entry.invalidated) {
      return 0;
    }
    return -EROFS;
  }
}

int RAMBackend::Seal(const std::string& oid, uint64_t epoch)
{
  std::lock_guard<std::mutex> lk(lock_);

  auto ret = objects_.emplace(oid, LogObject());
  auto& obj = boost::get<LogObject>(ret.first->second);

  // if exists, verify the new epoch is larger
  if (!ret.second) {
    if (epoch <= obj.epoch) {
      return -ESPIPE;
    }
  }

  obj.epoch = epoch;

  return 0;
}

int RAMBackend::MaxPos(const std::string& oid, uint64_t epoch,
    uint64_t *pos, bool *empty)
{
  std::lock_guard<std::mutex> lk(lock_);

  LogObject *lobj = nullptr;
  int ret = CheckEpoch(epoch, oid, true, lobj);
  if (ret) {
    return ret;
  }

  if (lobj) {
    bool is_empty = lobj->entries.empty();
    if (!is_empty)
      *pos = lobj->maxpos;
    *empty = is_empty;
  } else {
    *empty = true;
  }

  return 0;
}

int RAMBackend::AioWrite(const std::string& oid, uint64_t epoch,
    uint64_t position, const Slice& data, void *arg,
    std::function<void(void*, int)> callback)
{
  int ret = Write(oid, data, epoch, position);
  callback(arg, ret);
  return 0;
}

int RAMBackend::AioRead(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data, void *arg,
    std::function<void(void*, int)> callback)
{
  int ret = Read(oid, epoch, position, data);
  callback(arg, ret);
  return 0;
}


int RAMBackend::CheckEpoch(uint64_t epoch, const std::string& oid,
    bool eq, LogObject*& lobj)
{
  auto it = objects_.find(oid);
  if (it == objects_.end()) {
    return 0;
  }

  lobj = &boost::get<LogObject>(it->second);

  if (eq) { 
    if (epoch != lobj->epoch) {
      return -EINVAL;
    }
  } else if (epoch < lobj->epoch) {
    return -ESPIPE;
  }
  return 0;
}

extern "C" Backend *__backend_allocate(void)
{
  auto b = new RAMBackend();
  return b;
}

extern "C" void __backend_release(Backend *p)
{
  // TODO: whats the correct type of cast here
  RAMBackend *backend = (RAMBackend*)p;
  delete backend;
}

}
}
}
