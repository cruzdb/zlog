#include <sstream>
#include <iostream>
#include <iomanip>
#include <map>
#include <cstdlib>
#include "zlog/db.h"
#include "zlog/backend/ceph.h"
#include "zlog/backend/fakeseqr.h"

#define MAX_KEY 1000

static inline std::string tostr(int value)
{
  std::stringstream ss;
  ss << std::setw(3) << std::setfill('0') << value;
  return ss.str();
}

static void print_map(const std::map<std::string, std::string>& m)
{
  for (auto kv : m)
    std::cout << kv.first << " -> " << kv.second << std::endl;
}

static void check_history(const std::map<std::string, std::string>& a,
    const std::map<std::string, std::string>& b)
{
  if (a.size() != b.size()) {
    std::cout << "size " << a.size() << " != " << b.size() << std::endl;
    assert(0);
  }
  for (auto kv : a) {
    auto it = b.find(kv.first);
    if (it == b.end()) {
      print_map(b);
      std::cout << "key \"" << kv.first  << "\" not found" << std::endl;
      assert(0);
    }
    assert(kv.second == it->second);
  }
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
  delete it;
  return map;
}

static void test_seek(const std::map<std::string, std::string>& truth,
    DB *db, Snapshot *snapshot)
{
  assert(truth == get_map(db, snapshot, true, 0));

  for (int i = 0; i < 1000; i++) {
    int nkey = std::rand() % (MAX_KEY + 200); // 0-max+200
    std::string key = tostr(nkey);

    auto it = db->NewIterator(snapshot);
    it->Seek(key);

    auto it2 = truth.lower_bound(key);
    if (it2 == truth.end())
      assert(!it->Valid());
    else {
      assert(it->Valid());
      assert(it2->first == it->key());
    }

    delete it;
  }

  int nkey = std::rand() % (MAX_KEY + 100); // 0-max+100
  std::string key = tostr(nkey);

  auto it = db->NewIterator(snapshot);
  it->Seek(key);

  auto it2 = truth.lower_bound(key);
  if (it2 == truth.end()) {
    assert(!it->Valid());
    return;
  }

  while (it->Valid()) {
    assert(it->key() == it2->first);
    it->Next();
    it2++;
  }
  delete it;
  assert(it2 == truth.end());
}

int main(int argc, char **argv)
{
  unsigned max_txn_size = 1000;

  if (argc == 2) {
    max_txn_size = atoi(argv[1]);
    assert(max_txn_size > 0);
  }
  std::cout << "max num txns = " << max_txn_size << std::endl;

  std::srand(0);

  while (1) {
    std::vector<std::map<std::string, std::string>> truth_history;
    std::map<std::string, std::string> truth;
    truth_history.push_back(truth);

    // connect to rados
    librados::Rados cluster;
    cluster.init(NULL);
    cluster.conf_read_file(NULL);
    int ret = cluster.connect();
    assert(ret == 0);

    // open pool i/o context
    librados::IoCtx ioctx;
    ret = cluster.ioctx_create("zlog", ioctx);
    assert(ret == 0);

    zlog::Log *log;
    CephBackend *be = new CephBackend(&ioctx);
    auto client = new FakeSeqrClient();
    ret = zlog::Log::Create(be, "log", client, &log);
    assert(ret == 0);

    DB *db;
    ret = DB::Open(log, true, &db);
    assert(ret == 0);

    std::vector<Snapshot*> db_history;
    db_history.push_back(db->GetSnapshot());

    // number of transactions in tree
    int num_txns = std::rand() % max_txn_size;

    std::cout << "building tree with " <<
      num_txns << " transactions" << std::endl;
    std::cout << std::flush;

    while (num_txns--) {

      // number of operations in this transaction
      int num_ops = std::rand() % 10;

      auto txn = db->BeginTransaction();
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
      delete txn;

      truth_history.push_back(truth);
      db_history.push_back(db->GetSnapshot());
    }

    uint64_t count = 0;
    std::cout << "verifying tree...";
    std::cout << std::flush;
    assert(truth_history.size() == db_history.size());
    for (unsigned i = 0; i < db_history.size(); i++) {
      count += truth_history[i].size();
      check_history(truth_history[i], get_map(db, db_history[i], true, 0));
      assert(truth_history[i] == get_map(db, db_history[i], true, 0));
      assert(truth_history[i] == get_map(db, db_history[i], false, 0));
      if (truth_history[i].size() > 10) {
        size_t size = truth_history[i].size();
        assert(truth_history[i] == get_map(db, db_history[i], true, size));
        assert(truth_history[i] == get_map(db, db_history[i], false, size));
      }
      test_seek(truth_history[i], db, db_history[i]);
    }
    std::cout << " complete! (" << count << ")" << std::endl;

    for (Snapshot *snap : db_history) {
      db->ReleaseSnapshot(snap);
    }

    delete db;
    delete log;
    delete client;
    delete be;
  }

  return 0;
}
