#include <gtest/gtest.h>
#include <sstream>
#include <random>
#include <vector>
#include <map>
#include <unistd.h>
#include <stdlib.h>
#include "zlog/db.h"
#include "include/zlog/log.h"
#include "include/zlog/backend/lmdb.h"

#define MAX_KEY 1000

class TempDir {
 public:
  TempDir() {
    memset(path, 0, sizeof(path));
    sprintf(path, "/tmp/zlog.db.XXXXXX");
    assert(mkdtemp(path));
  }

  ~TempDir() {
    char cmd[64];
    memset(cmd, 0, sizeof(cmd));
    sprintf(cmd, "rm -rf %s", path);
    system(cmd);
  }

  char path[32];
};

static inline std::string tostr(int value)
{
  std::stringstream ss;
  ss << std::setw(3) << std::setfill('0') << value;
  return ss.str();
}

static std::map<std::string, std::string> get_map(DB *db,
    Snapshot *snapshot, bool forward, size_t split)
{
  std::map<std::string, std::string> map;
  auto it = db->NewIterator(snapshot);
  if (split > 0) {
    size_t half = split / 2;
    if (forward) {
      // skip forward half entries
      it->SeekToFirst();
      for (size_t i = 1; i < half; i++) {
        it->Next();
      }

      // insert that range moving backward
      assert(it->Valid());
      while (it->Valid()) {
        map[it->key().ToString()] = it->value().ToString();
        it->Prev();
      }

      // skip forward half entries
      it->SeekToFirst();
      for (size_t i = 0; i < half; i++) {
        it->Next();
      }
      assert(it->Valid());

      // add the last half
      while (it->Valid()) {
        map[it->key().ToString()] = it->value().ToString();
        it->Next();
      }
    } else {
      // skip back half entries
      it->SeekToLast();
      for (size_t i = 1; i < half; i++) {
        it->Prev();
      }

      // insert that range moving forward
      assert(it->Valid());
      while (it->Valid()) {
        map[it->key().ToString()] = it->value().ToString();
        it->Next();
      }

      // skip back half entries
      it->SeekToLast();
      for (size_t i = 0; i < half; i++) {
        it->Prev();
      }
      assert(it->Valid());

      // add the frst half
      while (it->Valid()) {
        map[it->key().ToString()] = it->value().ToString();
        it->Prev();
      }
    }
  } else {
    if (forward) {
      it->SeekToFirst();
      while (it->Valid()) {
        map[it->key().ToString()] = it->value().ToString();
        it->Next();
      }
    } else {
      it->SeekToLast();
      while (it->Valid()) {
        map[it->key().ToString()] = it->value().ToString();
        it->Prev();
      }
    }
  }
  return map;
}

static void test_seek(const std::map<std::string, std::string>& truth,
    DB *db, Snapshot *snapshot)
{
  for (int i = 0; i < 1000; i++) {
    int nkey = std::rand() % (MAX_KEY + 200); // 0-max+200
    std::string key = tostr(nkey);

    auto it = db->NewIterator(snapshot);
    it->Seek(key);

    auto it2 = truth.lower_bound(key);
    if (it2 == truth.end())
      ASSERT_TRUE(!it->Valid());
    else {
      ASSERT_TRUE(it->Valid());
      ASSERT_EQ(it2->first, it->key());
    }
  }

  int nkey = std::rand() % (MAX_KEY + 100); // 0-max+100
  std::string key = tostr(nkey);

  auto it = db->NewIterator(snapshot);
  it->Seek(key);

  auto it2 = truth.lower_bound(key);
  if (it2 == truth.end()) {
    ASSERT_TRUE(!it->Valid());
    return;
  }

  while (it->Valid()) {
    ASSERT_EQ(it->key(), it2->first);
    it->Next();
    it2++;
  }
  ASSERT_EQ(it2, truth.end());
}

/*
 * This test generates random transactions, saves a snapshot after each
 * transaction commits, and then verifies that the modification history is the
 * same as the equivalent database stored in an STL container.
 */
TEST(DB, EquivHistory) {
  TempDir tdir;

  // initial history is an empty stl database
  std::vector<std::map<std::string, std::string>> truth_history;
  std::map<std::string, std::string> truth;
  truth_history.push_back(truth);

  // initial empty kvstore database
  zlog::Log *log;
  auto be = new LMDBBackend("fakepool");
  be->Init(tdir.path, true);
  int ret = zlog::Log::Create(be, "log", NULL, &log);
  ASSERT_EQ(ret, 0);

  DB *db;
  ret = DB::Open(log, true, &db);
  ASSERT_EQ(ret, 0);

  std::vector<Snapshot*> db_history;
  db_history.push_back(db->GetSnapshot());

  // run transactions
  int num_txns = 200;
  while (num_txns--) {
    auto txn = db->BeginTransaction();
    // number of operations in this transaction
    int num_ops = std::rand() % 10;
    while (num_ops--) {
      // flip coin to insert or remove
      if ((std::rand() % 100) < 75) {
        // gen key/value pair to insert/update
        int nkey = (std::rand() % MAX_KEY) + 100; // so there is 0-100 unused
        std::string key = tostr(nkey);
        int nval = std::rand() % 1000;
        std::string val = tostr(nval);
        truth[key] = val;
        txn->Put(key, val);
      } else {
        // remove things that are actually in tree
        if (truth.empty())
          continue;
        auto it = truth.begin();
        std::advance(it, std::rand() % truth.size());
        assert(it != truth.end());
        std::string key = it->first;
        truth.erase(it);
        txn->Delete(key);
      }
    }
    txn->Commit();

    truth_history.push_back(truth);
    db_history.push_back(db->GetSnapshot());
  }

  ASSERT_EQ(truth_history.size(), db_history.size());

  for (unsigned i = 0; i < db_history.size(); i++) {
    ASSERT_EQ(truth_history[i], get_map(db, db_history[i], true, 0));
    ASSERT_EQ(truth_history[i], get_map(db, db_history[i], false, 0));
    if (truth_history[i].size() > 10) {
      size_t size = truth_history[i].size();
      ASSERT_EQ(truth_history[i], get_map(db, db_history[i], true, size));
      ASSERT_EQ(truth_history[i], get_map(db, db_history[i], false, size));
    }
    test_seek(truth_history[i], db, db_history[i]);
  }
}

TEST(DB, Iterator) {
  TempDir tdir;

  zlog::Log *log;
  auto be = new LMDBBackend("fakepool");
  be->Init(tdir.path, true);
  int ret = zlog::Log::Create(be, "log", NULL, &log);
  ASSERT_EQ(ret, 0);

  DB *db;
  ret = DB::Open(log, true, &db);
  ASSERT_EQ(ret, 0);

  std::vector<std::string> strs{"m", "f", "t"};
  for (auto s : strs) {
    auto txn = db->BeginTransaction();
    txn->Put(s, "");
    txn->Commit();
  }

  auto it = db->NewIterator();
  ASSERT_TRUE(!it->Valid());

  // equality
  it->Seek("m");
  ASSERT_TRUE(it->Valid());
  ASSERT_EQ(it->key(), "m");

  it->Seek("f");
  ASSERT_TRUE(it->Valid());
  ASSERT_EQ(it->key(), "f");

  it->Seek("t");
  ASSERT_TRUE(it->Valid());
  ASSERT_EQ(it->key(), "t");

  // edges
  it->Seek("a");
  ASSERT_TRUE(it->Valid());
  ASSERT_EQ(it->key(), "f");

  it->Seek("h");
  ASSERT_TRUE(it->Valid());
  ASSERT_EQ(it->key(), "m");

  it->Seek("j");
  ASSERT_TRUE(it->Valid());
  ASSERT_EQ(it->key(), "m");

  it->Seek("o");
  ASSERT_TRUE(it->Valid());
  ASSERT_EQ(it->key(), "t");

  it->Seek("v");
  ASSERT_TRUE(!it->Valid());

  it->Seek("x");
  ASSERT_TRUE(!it->Valid());
}

TEST(DB, Get) {
  TempDir tdir;

  zlog::Log *log;
  auto be = new LMDBBackend("fakepool");
  be->Init(tdir.path, true);
  int ret = zlog::Log::Create(be, "log", NULL, &log);
  ASSERT_EQ(ret, 0);

  DB *db;
  ret = DB::Open(log, true, &db);
  ASSERT_EQ(ret, 0);

  std::vector<std::string> strs{"a", "b", ""};
  for (auto s : strs) {
    auto txn = db->BeginTransaction();
    txn->Put(s, s.empty() ? "Empty key" : s);
    txn->Commit();
  }

  auto txn = db->BeginTransaction();
  std::string val;

  // empty key
  ret = txn->Get("", &val);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(val, "Empty key");

  // c does not exist
  ret = txn->Get("c", &val);
  ASSERT_EQ(ret, -ENOENT);

  // a exists
  ret = txn->Get("a", &val);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(val, "a");

  // b exists
  ret = txn->Get("b", &val);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(val, "b");

  txn->Commit();
}

TEST(DB, ReOpen) {
  TempDir tdir;

  // populate a database and close it
  std::map<std::string, std::string> prev_db;
  {
    auto *be = new LMDBBackend("fakepool");
    be->Init(tdir.path, true);

    zlog::Log *log;
    int ret = zlog::Log::Create(be, "log", NULL, &log);
    ASSERT_EQ(ret, 0);

    DB *db;
    ret = DB::Open(log, true, &db);
    ASSERT_EQ(0, ret);

    for (int i = 0; i < 100; i++) {
      std::stringstream ss;
      ss << "key-" << i;
      std::string key = ss.str();
      ss << "-val";
      std::string val = ss.str();

      auto *txn = db->BeginTransaction();

      std::string val_out;
      ret = txn->Get(key, &val_out);
      ASSERT_EQ(-ENOENT, ret);

      txn->Put(key, val);
      prev_db[key] = val;

      txn->Commit();
      delete txn;
    }

    delete db;
    delete log;
    be->Close();
    delete be;
  }

  // re-open the database and verify the previous inserts
  auto *be = new LMDBBackend("fakepool");
  be->Init(tdir.path, false);

  zlog::Log *log;
  int ret = zlog::Log::Open(be, "log", NULL, &log);
  ASSERT_EQ(ret, 0);

  DB *db;
  ret = DB::Open(log, false, &db);
  ASSERT_EQ(ret, 0);

  std::map<std::string, std::string> curr_db;
  auto *it = db->NewIterator();
  it->SeekToFirst();
  while (it->Valid()) {
    curr_db[it->key().ToString()] = it->value().ToString();
    it->Next();
  }

  ASSERT_EQ(prev_db, curr_db);

  delete db;
  delete log;
  be->Close();
  delete be;
}
