#include <vector>
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

// TODO: backend needs to be OK with being deleted before having been
// initialized...
LMDBBackend::~LMDBBackend()
{
  if (!closed) {
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

int LMDBBackend::CreateLog(const std::string& name,
    const std::string& initial_view)
{
  auto txn = NewTransaction();

  MDB_val val;
  std::string oid_key = ObjectKey(name);
  int ret = txn.Get(oid_key, val);
  if (!ret) {
    txn.Abort();
    return -EEXIST;
  }

  ProjectionObject proj_obj;
  val.mv_data = &proj_obj;
  val.mv_size = sizeof(proj_obj);
  ret = txn.Put(oid_key, val, true);
  if (ret) {
    txn.Abort();
    return ret;
  }

  std::string proj_key = ProjectionKey(name,
      proj_obj.latest_epoch);
  val.mv_data = (void*)initial_view.data();
  val.mv_size = initial_view.size();
  ret = txn.Put(proj_key, val, true);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ret = txn.Commit();
  if (ret)
    return ret;

  return 0;
}

int LMDBBackend::OpenLog(const std::string& name,
    std::string& hoid, std::string& prefix)
{
  auto txn = NewTransaction();

  MDB_val val;
  std::string oid_key = ObjectKey(name);
  int ret = txn.Get(oid_key, val);
  if (ret) {
    txn.Abort();
    return ret;
  }

  txn.Abort();

  hoid = name;
  prefix = name;

  return 0;
}

int LMDBBackend::ReadViews(const std::string& hoid, uint64_t epoch,
    std::map<uint64_t, std::string>& views)
{
  auto txn = NewTransaction(true);

  MDB_val val;
  std::string oid_key = ObjectKey(hoid);
  int ret = txn.Get(oid_key, val);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ProjectionObject *proj_obj = (ProjectionObject*)val.mv_data;
  assert(val.mv_size == sizeof(*proj_obj));

  if (epoch > proj_obj->latest_epoch) {
    txn.Abort();
    return 0;
  }

  std::string proj_key = ProjectionKey(hoid, epoch);
  ret = txn.Get(proj_key, val);
  if (ret) {
    txn.Abort();
    return ret;
  }

  views.emplace(epoch,
      std::string((const char *)val.mv_data, val.mv_size));

  ret = txn.Commit();
  if (ret)
    return ret;

  return 0;
}

int LMDBBackend::ProposeView(const std::string& hoid,
    uint64_t epoch, const std::string& view)
{
  auto txn = NewTransaction();

  MDB_val val;
  std::string oid_key = ObjectKey(hoid);
  int ret = txn.Get(oid_key, val);
  if (ret) {
    if (ret == -ENOENT) {
      assert(epoch == 0);
    } else {
      txn.Abort();
      return ret;
    }
  }

  // there is a case for handling enoent in the distributed version, but it
  // seems we do not need that case for the lmdb backend, yet.
  assert(ret == 0);

  ProjectionObject *proj_obj = (ProjectionObject*)val.mv_data;
  assert(val.mv_size == sizeof(*proj_obj));
  assert(epoch == (proj_obj->latest_epoch + 1));

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

  proj_obj->latest_epoch = epoch;
  val.mv_data = proj_obj;
  val.mv_size = sizeof(*proj_obj);
  ret = txn.Put(oid_key, val, false);
  if (ret) {
    txn.Abort();
    return ret;
  }

  txn.Commit();
  return 0;
}

int LMDBBackend::Write(const std::string& oid, const Slice& data,
    uint64_t epoch, uint64_t position, uint32_t stride, uint32_t max_size)
{
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
    uint64_t position, uint32_t stride, uint32_t max_size,
    std::string *data)
{
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
    return ret;
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
    uint64_t position, uint32_t stride, uint32_t max_size)
{
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
    uint64_t position, uint32_t stride, uint32_t max_size)
{
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

int LMDBBackend::AioWrite(const std::string& oid, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size,
    const Slice& data, void *arg,
    std::function<void(void*, int)> callback)
{
  int ret = Write(oid, data, epoch, position, stride, max_size);
  callback(arg, ret);
  return 0;
}

int LMDBBackend::AioRead(const std::string& oid, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size,
    std::string *data, void *arg,
    std::function<void(void*, int)> callback)
{
  int ret = Read(oid, epoch, position, stride, max_size, data);
  callback(arg, ret);
  return 0;
}

int LMDBBackend::CheckEpoch(Transaction& txn, uint64_t epoch,
    const std::string& oid, bool eq)
{
  MDB_val val;
  auto key = ObjectKey(oid);
  int ret = txn.Get(key, val);
  if (ret == -ENOENT)
    return 0;
  LogObject *obj = (LogObject*)val.mv_data;
  assert(val.mv_size == sizeof(*obj));
  if (eq) { 
    if (epoch != obj->epoch) {
      return -EINVAL;
    }
  } else if (epoch < obj->epoch) {
    return -ESPIPE;
  }
  return 0;
}

int LMDBBackend::MaxPos(const std::string& oid, uint64_t epoch,
    uint64_t *pos, bool *empty)
{
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
  auto txn = NewTransaction();

  // read current epoch value (if its been set yet)
  MDB_val val;
  auto key = ObjectKey(oid);
  int ret = txn.Get(key, val);
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
  txn.Put(key, val, false);

  ret = txn.Commit();
  if (ret)
    return ret;

  return 0;
}

void LMDBBackend::Init(const std::string& path)
{
  // TODO: even when a backend is created explicitly, it needs to fill in enough
  // options so that a sequencer can open an instance. Or not. In our case def.
  options["path"] = path;

  int ret = mdb_env_create(&env);
  assert(ret == 0);
  (void)ret;

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
  closed = true;
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
  // TODO: whats the correct type of cast here
  LMDBBackend *backend = (LMDBBackend*)p;
  delete backend;
}

}
}
}
