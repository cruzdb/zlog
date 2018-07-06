#include <vector>
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
    uint64_t position, uint32_t stride, uint32_t max_size,
    std::string *data)
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

int RAMBackend::Write(const std::string& oid, const Slice& data,
    uint64_t epoch, uint64_t position, uint32_t stride, uint32_t max_size)
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

int RAMBackend::Trim(const std::string& oid, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size)
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
    uint64_t position, uint32_t stride, uint32_t max_size)
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
    uint64_t position, uint32_t stride, uint32_t max_size,
    const Slice& data, void *arg,
    std::function<void(void*, int)> callback)
{
  int ret = Write(oid, data, epoch, position, stride, max_size);
  callback(arg, ret);
  return 0;
}

int RAMBackend::AioRead(const std::string& oid, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size,
    std::string *data, void *arg,
    std::function<void(void*, int)> callback)
{
  int ret = Read(oid, epoch, position, stride, max_size, data);
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
