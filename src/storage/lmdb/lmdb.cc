#include <vector>
#include <atomic>
#include <cassert>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <lmdb.h>
#include "zlog/backend.h"
#include "zlog/backend/lmdb.h"

namespace zlog {
namespace storage {
namespace lmdb {

#define ZLOG_LMDB_ASSERT(ret, cond) do { \
  if (!(cond)) { \
    std::cerr << mdb_strerror(ret) << std::endl; \
    assert(0); \
  } } while (0)

#define ZLOG_COMMIT(txn) do { \
  int __ret = mdb_txn_commit(txn); \
  ZLOG_LMDB_ASSERT(__ret, __ret == 0); \
  } while (0)

LMDBBackend::Transaction LMDBBackend::NewTransaction(bool read_only)
{
  MDB_txn *txn;
  int flags = read_only ? MDB_RDONLY : 0;
  int ret = mdb_txn_begin(env, NULL, flags, &txn);
  assert(ret == 0);
  (void)ret;
  return Transaction(txn, this);
}

LMDBBackend::~LMDBBackend()
{
  if (need_close) {
    Close();
  }
}

std::map<std::string, std::string> LMDBBackend::meta()
{
  return options;
}

int LMDBBackend::Initialize(
    const std::map<std::string, std::string>& opts)
{
  auto it = opts.find("path");
  if (it == opts.end())
    return -EINVAL;

  Init(it->second);

  return 0;
}

int LMDBBackend::uniqueId(const std::string& hoid, uint64_t *id)
{
  if (hoid.empty()) {
    return -EINVAL;
  }

  static std::atomic<uint64_t> __unique_id(0);
  *id = __unique_id++;

  return 0;
}

int LMDBBackend::CreateLog(const std::string& name, const std::string& view,
    std::string *hoid_out, std::string *prefix_out)
{
  if (name.empty()) {
    return -EINVAL;
  }

  boost::uuids::uuid uuid = boost::uuids::random_generator()();
  const auto key = boost::uuids::to_string(uuid);
  auto hoid = std::string("zlog.head.").append(key);
  auto prefix = std::string("zlog.data.").append(key);

  auto txn = NewTransaction();

  ProjectionObject proj_obj;
  proj_obj.epoch = 1;
  strcpy(proj_obj.prefix, prefix.c_str());

  MDB_val val;
  val.mv_data = &proj_obj;
  val.mv_size = sizeof(proj_obj);
  int ret = txn.Put(hoid, val, true);
  if (ret) {
    txn.Abort();
    if (ret == -EEXIST) {
      // ensure unique hoid. a more robust implementation can
      // retry generating a unique object name.
      return -EIO;
    }
    return ret;
  }

  std::string proj_key = ProjectionKey(hoid, proj_obj.epoch);
  val.mv_data = (void*)view.data();
  val.mv_size = view.size();
  ret = txn.Put(proj_key, val, true);
  if (ret) {
    txn.Abort();
    return ret;
  }

  auto prefixed_name = std::string("head.").append(name);
  LinkObject link;
  strcpy(link.hoid, hoid.c_str());
  val.mv_data = &link;
  val.mv_size = sizeof(link);
  ret = txn.Put(prefixed_name, val, true);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ret = txn.Commit();
  if (ret) {
    return ret;
  }

  if (hoid_out) {
    *hoid_out = hoid;
  }

  if (prefix_out) {
    *prefix_out = prefix;
  }

  return 0;
}

int LMDBBackend::OpenLog(const std::string& name, std::string *hoid_out,
    std::string *prefix_out)
{
  if (name.empty()) {
    return -EINVAL;
  }

  auto txn = NewTransaction();

  auto prefixed_name = std::string("head.").append(name);
  MDB_val val;
  int ret = txn.Get(prefixed_name, val);
  if (ret) {
    txn.Abort();
    return ret;
  }

  LinkObject *link = (LinkObject*)val.mv_data;
  std::string hoid(link->hoid);

  ret = txn.Get(hoid, val);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ProjectionObject *proj = (ProjectionObject*)val.mv_data;
  std::string prefix(proj->prefix);

  ret = txn.Commit();
  if (ret) {
    return ret;
  }

  if (hoid_out) {
    *hoid_out = hoid;
  }

  if (prefix_out) {
    *prefix_out = prefix;
  }

  return 0;
}
int LMDBBackend::ListLinks(std::vector<std::string> &loids_out) {
  auto txn = NewTransaction(true);
  std::vector<MDB_val> keys;
  int ret = txn.GetAll("head.", keys);
  if (ret) {
    txn.Abort();
    return ret;
  }
  std::transform(keys.cbegin(), keys.cend(), std::back_inserter(loids_out), [](MDB_val key) {
    return std::string(reinterpret_cast<const char *>(key.mv_data), key.mv_size);
  });
  return txn.Commit();
}

int LMDBBackend::ListHeads(std::vector<std::string> &ooids_out) {
  auto txn = NewTransaction(true);
  std::vector<MDB_val> keys;
  std::string prefix("zlog.head.");
  int ret = txn.GetAll(prefix, keys);
  if (ret) {
    txn.Abort();
    return ret;
  }
  size_t prefixLength = prefix.size();
  for (auto &key : keys) {
    std::string prefixStripped(reinterpret_cast<const char*>(key.mv_data) + prefixLength, key.mv_size - prefixLength);
    // Filter out 'zlog.head.*.N'
    if (prefixStripped.find('.') != std::string::npos) {
      continue;
    }
    ooids_out.emplace_back(reinterpret_cast<const char*>(key.mv_data), key.mv_size);
  }
  return txn.Commit();
}

int LMDBBackend::ReadViews(const std::string& hoid, uint64_t epoch,
    uint32_t max_views, std::map<uint64_t, std::string> *views_out)
{
  if (hoid.empty()) {
    return -EINVAL;
  }

  if (epoch == 0) {
    return -EINVAL;
  }

  auto txn = NewTransaction(true);

  MDB_val val;
  int ret = txn.Get(hoid, val);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ProjectionObject *proj_obj = (ProjectionObject*)val.mv_data;
  assert(val.mv_size == sizeof(*proj_obj));

  std::map<uint64_t, std::string> views;
  if (epoch > proj_obj->epoch) {
    views_out->swap(views);
    txn.Abort();
    return 0;
  }

  uint32_t count = 0;
  while (true) {
    if (count == max_views) {
      break;
    }

    std::string proj_key = ProjectionKey(hoid, epoch);
    ret = txn.Get(proj_key, val);
    if (ret) {
      if (ret == -ENOENT) {
        break;
      }
      txn.Abort();
      return ret;
    }

    views.emplace(epoch,
        std::string((const char *)val.mv_data, val.mv_size));

    count++;
    epoch++;
  }

  ret = txn.Commit();
  if (ret)
    return ret;

  views_out->swap(views);

  return 0;
}

int LMDBBackend::ProposeView(const std::string& hoid,
    uint64_t epoch, const std::string& view)
{
  if (hoid.empty()) {
    return -EINVAL;
  }

  if (epoch == 0) {
    return -EINVAL;
  }

  auto txn = NewTransaction();

  MDB_val val;
  int ret = txn.Get(hoid, val);
  if (ret) {
    if (ret == -ENOENT) {
      txn.Abort();
      return ret;
    } else {
      txn.Abort();
      return ret;
    }
  }

  ProjectionObject *proj_obj = (ProjectionObject*)val.mv_data;
  assert(val.mv_size == sizeof(*proj_obj));

  const auto required_epoch = proj_obj->epoch + 1;
  if (epoch > required_epoch) {
    txn.Abort();
    return -EINVAL;
  }
  if (epoch != required_epoch) {
    txn.Abort();
    return -ESPIPE;
  }

  // write new projection
  MDB_val proj_val;
  std::string proj_key = ProjectionKey(hoid, epoch);
  proj_val.mv_data = (void*)view.data();
  proj_val.mv_size = view.size();
  ret = txn.Put(proj_key, proj_val, true);
  if (ret) {
    txn.Abort();
    return ret;
  }

  proj_obj->epoch = epoch;
  val.mv_data = proj_obj;
  val.mv_size = sizeof(*proj_obj);
  ret = txn.Put(hoid, val, false);
  if (ret) {
    txn.Abort();
    return ret;
  }

  txn.Commit();
  return 0;
}

int LMDBBackend::Write(const std::string& oid, const std::string& data,
    uint64_t epoch, uint64_t position)
{
  if (oid.empty()) {
    return -EINVAL;
  }

  if (epoch == 0) {
    return -EINVAL;
  }

  auto txn = NewTransaction();

  int ret = CheckEpoch(txn, epoch, oid);
  if (ret) {
    txn.Abort();
    return ret;
  }

  // read max position
  uint64_t pos = 0;
  MDB_val maxval;
  auto maxkey = MaxPosKey(oid);
  ret = txn.Get(maxkey, maxval);
  // TODO: enoent here?
  if (ret < 0 && ret != -ENOENT) {
    txn.Abort();
    return ret;
  } else if (ret == 0) {
    LogMaxPos *maxpos = (LogMaxPos*)maxval.mv_data;
    assert(maxval.mv_size == sizeof(*maxpos));
    pos = maxpos->maxpos;
  }

  LogEntry entry;
  const size_t size = sizeof(entry) + data.size();
  std::vector<unsigned char> blob;
  blob.reserve(size);
  blob.insert(blob.end(), (unsigned char *)&entry,
      ((unsigned char *)&entry) + sizeof(entry));
  blob.insert(blob.end(), (unsigned char *)data.data(),
      ((unsigned char *)data.data()) + data.size());

  std::string key = LogEntryKey(oid, position);
  ret = txn.Put(key, blob, true);
  if (ret == -EEXIST) {
    txn.Abort();
    return -EROFS;
  }

  // update max pos
  LogMaxPos new_maxpos;
  new_maxpos.maxpos = std::max(pos, position);
  maxval.mv_data = &new_maxpos;
  maxval.mv_size = sizeof(new_maxpos);
  txn.Put(maxkey, maxval, false);

  ret = txn.Commit();
  if (ret)
    return ret;

  return 0;
}

int LMDBBackend::Read(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data)
{
  if (oid.empty()) {
    return -EINVAL;
  }

  if (epoch == 0) {
    return -EINVAL;
  }

  auto txn = NewTransaction(true);

  int ret = CheckEpoch(txn, epoch, oid);
  if (ret) {
    txn.Abort();
    return ret;
  }

  MDB_val val;
  std::string key = LogEntryKey(oid, position);
  ret = txn.Get(key, val);
  if (ret == -ENOENT) {
    txn.Abort();
    return -ERANGE;
  }

  LogEntry *entry = (LogEntry*)val.mv_data;
  if (entry->trimmed || entry->invalidated) {
    txn.Abort();
    return -ENODATA;
  }

  if (data) {
    const char *blob = (const char *)val.mv_data + sizeof(*entry);
    data->assign(blob, val.mv_size - sizeof(*entry));
  }

  ret = txn.Commit();
  if (ret)
    return ret;

  return 0;
}

int LMDBBackend::Trim(const std::string& oid, uint64_t epoch,
    uint64_t position)
{
  if (oid.empty()) {
    return -EINVAL;
  }

  if (epoch == 0) {
    return -EINVAL;
  }

  auto txn = NewTransaction();

  int ret = CheckEpoch(txn, epoch, oid);
  if (ret) {
    txn.Abort();
    return ret;
  }

  LogEntry entry;

  MDB_val val;
  std::string key = LogEntryKey(oid, position);
  ret = txn.Get(key, val);
  if (!ret) {
    assert(val.mv_size >= sizeof(entry));
    entry = *((LogEntry*)val.mv_data);
  }

  // read max position
  uint64_t pos = 0;
  MDB_val maxval;
  auto maxkey = MaxPosKey(oid);
  ret = txn.Get(maxkey, maxval);
  if (ret < 0 && ret != -ENOENT) {
    txn.Abort();
    return ret;
  } else if (ret == 0) {
    LogMaxPos *maxpos = (LogMaxPos*)maxval.mv_data;
    assert(maxval.mv_size == sizeof(*maxpos));
    pos = maxpos->maxpos;
  }

  // update max pos
  LogMaxPos new_maxpos;
  new_maxpos.maxpos = std::max(pos, position);
  maxval.mv_data = &new_maxpos;
  maxval.mv_size = sizeof(new_maxpos);
  txn.Put(maxkey, maxval, false);

  entry.trimmed = true;

  val.mv_size = sizeof(entry);
  val.mv_data = &entry;

  ret = txn.Put(key, val, false);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ret = txn.Commit();
  if (ret)
    return ret;

  return 0;
}

int LMDBBackend::Fill(const std::string& oid, uint64_t epoch,
    uint64_t position)
{
  if (oid.empty()) {
    return -EINVAL;
  }

  if (epoch == 0) {
    return -EINVAL;
  }

  auto txn = NewTransaction();

  int ret = CheckEpoch(txn, epoch, oid);
  if (ret) {
    txn.Abort();
    return ret;
  }

  LogEntry entry;

  MDB_val val;
  std::string key = LogEntryKey(oid, position);
  ret = txn.Get(key, val);
  if (!ret) {
    assert(val.mv_size >= sizeof(entry));
    entry = *((LogEntry*)val.mv_data);
    if (entry.trimmed || entry.invalidated) {
      txn.Abort();
      return 0;
    }
    txn.Abort();
    return -EROFS;
  }

  // read max position
  uint64_t pos = 0;
  MDB_val maxval;
  auto maxkey = MaxPosKey(oid);
  ret = txn.Get(maxkey, maxval);
  if (ret < 0 && ret != -ENOENT) {
    txn.Abort();
    return ret;
  } else if (ret == 0) {
    LogMaxPos *maxpos = (LogMaxPos*)maxval.mv_data;
    assert(maxval.mv_size == sizeof(*maxpos));
    pos = maxpos->maxpos;
  }

  // update max pos
  LogMaxPos new_maxpos;
  new_maxpos.maxpos = std::max(pos, position);
  maxval.mv_data = &new_maxpos;
  maxval.mv_size = sizeof(new_maxpos);
  txn.Put(maxkey, maxval, false);

  entry.trimmed = true;
  entry.invalidated = true;

  val.mv_size = sizeof(entry);
  val.mv_data = &entry;

  ret = txn.Put(key, val, false);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ret = txn.Commit();
  if (ret)
    return ret;

  return 0;
}

int LMDBBackend::CheckEpoch(Transaction& txn, uint64_t epoch,
    const std::string& oid, bool eq)
{
  MDB_val val;
  int ret = txn.Get(oid, val);
  if (ret == -ENOENT)
    return ret;
  LogObject *obj = (LogObject*)val.mv_data;
  assert(val.mv_size == sizeof(*obj));
  if (eq) { 
    if (epoch != obj->epoch) {
      return -ESPIPE;
    }
  } else if (epoch < obj->epoch) {
    return -ESPIPE;
  }
  return 0;
}

int LMDBBackend::MaxPos(const std::string& oid, uint64_t epoch,
    uint64_t *pos, bool *empty)
{
  if (oid.empty()) {
    return -EINVAL;
  }

  if (epoch == 0) {
    return -EINVAL;
  }

  auto txn = NewTransaction(true);

  int ret = CheckEpoch(txn, epoch, oid, true);
  if (ret) {
    txn.Abort();
    return ret;
  }

  MDB_val val;
  auto key = MaxPosKey(oid);
  ret = txn.Get(key, val);
  if (ret < 0) {
    if (ret == -ENOENT) {
      *empty = true;
      txn.Commit();
      return 0;
    }
    txn.Abort();
    return ret;
  }

  LogMaxPos *maxpos = (LogMaxPos*)val.mv_data;
  assert(val.mv_size == sizeof(*maxpos));
  txn.Commit();
  *pos = maxpos->maxpos;
  *empty = false;

  return 0;
}

int LMDBBackend::Seal(const std::string& oid, uint64_t epoch)
{
  if (oid.empty()) {
    return -EINVAL;
  }

  if (epoch == 0) {
    return -EINVAL;
  }

  auto txn = NewTransaction();

  // read current epoch value (if its been set yet)
  MDB_val val;
  int ret = txn.Get(oid, val);
  assert(ret == 0 || ret == -ENOENT);

  // if exists, verify the new epoch is larger
  LogObject obj;
  if (ret == 0) {
    assert(val.mv_size == sizeof(obj));
    obj = *((LogObject*)val.mv_data);
    if (epoch <= obj.epoch) {
      txn.Abort();
      return -ESPIPE;
    }
  }

  // write new epoch
  obj.epoch = epoch;
  val.mv_data = &obj;
  val.mv_size = sizeof(obj);
  txn.Put(oid, val, false);

  ret = txn.Commit();
  if (ret)
    return ret;

  return 0;
}

void LMDBBackend::Init(const std::string& path)
{
  options["path"] = path;

  int ret = mdb_env_create(&env);
  assert(ret == 0);
  (void)ret;

  need_close = true;

  ret = mdb_env_set_maxdbs(env, 2);
  assert(ret == 0);

  size_t gbs = 1;
  char *size_str = getenv("ZLOG_LMDB_BE_SIZE");
  if (size_str) {
    gbs = atoi(size_str);
  }

  gbs = gbs << 30;
  ret = mdb_env_set_mapsize(env, gbs);
  assert(ret == 0);

  unsigned int flags = MDB_NOTLS | MDB_NOSYNC | MDB_NOMETASYNC | MDB_WRITEMAP | MDB_NOMEMINIT;
  ret = mdb_env_open(env, path.c_str(), flags, 0644);
  assert(ret == 0);

  MDB_txn *txn;
  ret = mdb_txn_begin(env, NULL, 0, &txn);
  assert(ret == 0);

  ret = mdb_dbi_open(txn, "objs", MDB_CREATE, &db_obj);
  assert(ret == 0);

  ret = mdb_txn_commit(txn);
  assert(ret == 0);
}

void LMDBBackend::Close()
{
  need_close = false;
  mdb_env_sync(env, 1);
  mdb_env_close(env);
}

extern "C" Backend *__backend_allocate(void)
{
  auto b = new LMDBBackend();
  return b;
}

extern "C" void __backend_release(Backend *p)
{
  LMDBBackend *backend = (LMDBBackend*)p;
  delete backend;
}

}
}
}
