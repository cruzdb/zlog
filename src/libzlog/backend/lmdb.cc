#include <vector>
#include <lmdb.h>
#include "zlog/backend.h"
#include "zlog/backend/lmdb.h"

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
  return Transaction(txn, this);
}

int LMDBBackend::Exists(const std::string& oid)
{
  auto txn = NewTransaction(true);

  auto key = ObjectKey(oid);

  MDB_val val;
  int ret = txn.Get(key, val);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ret = txn.Commit();
  if (ret)
    return ret;

  return ZLOG_OK;
}

int LMDBBackend::CreateHeadObject(const std::string& oid,
    const zlog_proto::MetaLog& data)
{
  std::string blob;
  assert(data.IsInitialized());
  assert(data.SerializeToString(&blob));

  auto txn = NewTransaction();

  MDB_val val;
  std::string oid_key = ObjectKey(oid);
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

  std::string proj_key = ProjectionKey(oid,
      proj_obj.latest_epoch);
  val.mv_data = (void*)blob.data();
  val.mv_size = blob.size();
  ret = txn.Put(proj_key, val, true);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ret = txn.Commit();
  if (ret)
    return ret;

  return ZLOG_OK;
}

int LMDBBackend::LatestProjection(const std::string& oid,
    uint64_t *epoch, zlog_proto::MetaLog& config)
{
  auto txn = NewTransaction(true);

  MDB_val val;
  std::string oid_key = ObjectKey(oid);
  int ret = txn.Get(oid_key, val);
  if (ret) {
    txn.Abort();
    return ret;
  }

  ProjectionObject *proj_obj = (ProjectionObject*)val.mv_data;
  assert(val.mv_size == sizeof(*proj_obj));

  std::string proj_key = ProjectionKey(oid, proj_obj->latest_epoch);
  ret = txn.Get(proj_key, val);
  if (ret) {
    txn.Abort();
    return ret;
  }

  *epoch = proj_obj->latest_epoch;
  assert(config.ParseFromArray(val.mv_data, val.mv_size));

  ret = txn.Commit();
  if (ret)
    return ret;

  return ZLOG_OK;
}

int LMDBBackend::Write(const std::string& oid, const Slice& data,
    uint64_t epoch, uint64_t position)
{
  auto txn = NewTransaction();

  int ret = CheckEpoch(txn, epoch, oid);
  if (ret) {
    txn.Abort();
    return ret;
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
    return Backend::ZLOG_READ_ONLY;
  }

  ret = txn.Commit();
  if (ret)
    return ret;

  return ZLOG_OK;
}

int LMDBBackend::Read(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data)
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
    return ZLOG_NOT_WRITTEN;
  }

  LogEntry *entry = (LogEntry*)val.mv_data;
  if (entry->trimmed || entry->invalidated) {
    txn.Abort();
    return ZLOG_INVALIDATED;
  }

  if (data) {
    const char *blob = (const char *)val.mv_data + sizeof(*entry);
    data->assign(blob, val.mv_size - sizeof(*entry));
  }

  ret = txn.Commit();
  if (ret)
    return ret;

  return ZLOG_OK;
}

int LMDBBackend::Trim(const std::string& oid, uint64_t epoch,
    uint64_t position)
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

  return ZLOG_OK;
}

int LMDBBackend::Fill(const std::string& oid, uint64_t epoch,
    uint64_t position)
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
      return ZLOG_OK;
    }
    txn.Abort();
    return ZLOG_READ_ONLY;
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

  return ZLOG_OK;
}

int LMDBBackend::AioAppend(const std::string& oid, uint64_t epoch,
    uint64_t position, const Slice& data, void *arg,
    std::function<void(void*, int)> callback)
{
  int ret = Write(oid, data, epoch, position);
  callback(arg, ret);
  return ZLOG_OK;
}

int LMDBBackend::AioRead(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data, void *arg,
    std::function<void(void*, int)> callback)
{
  int ret = Read(oid, epoch, position, data);
  callback(arg, ret);
  return ZLOG_OK;
}

int LMDBBackend::CheckEpoch(Transaction& txn, uint64_t epoch,
    const std::string& oid)
{
  MDB_val val;
  auto key = ObjectKey(oid);
  int ret = txn.Get(key, val);
  if (ret == -ENOENT)
    return 0;
  LogObject *obj = (LogObject*)val.mv_data;
  assert(val.mv_size == sizeof(*obj));
  if (obj->sealed && epoch <= obj->epoch)
    return Backend::ZLOG_STALE_EPOCH;
  return 0;
}

void LMDBBackend::Init(bool empty)
{
  int ret = mdb_env_create(&env);
  assert(ret == 0);

  ret = mdb_env_set_maxdbs(env, 2);
  assert(ret == 0);

  ret = mdb_env_set_mapsize(env, 1<<30);
  assert(ret == 0);

  unsigned int flags = MDB_MAPASYNC | MDB_WRITEMAP | MDB_NOMEMINIT;
  ret = mdb_env_open(env, "db", flags, 0644);
  assert(ret == 0);

  MDB_txn *txn;
  ret = mdb_txn_begin(env, NULL, 0, &txn);
  assert(ret == 0);

  ret = mdb_dbi_open(txn, "objs", MDB_CREATE, &db_obj);
  assert(ret == 0);

  if (empty) {
    ret = mdb_drop(txn, db_obj, 0);
    assert(ret == 0);
  }

  ret = mdb_txn_commit(txn);
  assert(ret == 0);
}

void LMDBBackend::Close()
{
  mdb_env_close(env);
}
