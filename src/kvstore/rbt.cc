#include <sstream>
#include <iomanip>
#include <iostream>
#include "zlog/db.h"
#include "zlog/backend/lmdb.h"
#include "zlog/backend/fakeseqr.h"

static inline std::string tostr(int value)
{
  std::stringstream ss;
  ss << std::setw(3) << std::setfill('0') << value;
  return ss.str();
}

int main(int argc, char **argv)
{
  zlog::Log *log;
  auto client = new FakeSeqrClient();
  auto be = new LMDBBackend("fakepool");
  be->Init("/tmp/zlog.bench.db", false);
  int ret = zlog::Log::OpenOrCreate(be, "log", client, &log);
  assert(ret == 0);
  client->Init(log, "fakepool", "log");

  DB *db;
  ret = DB::Open(log, true, &db);
  assert(ret == 0);

  std::vector<Snapshot*> snapshots;
  snapshots.push_back(db->GetSnapshot());

  int num_txns = 20;
  while (num_txns--) {

    // number of operations in this transaction
    int num_ops = std::rand() % 10;
    auto txn = db->BeginTransaction();
    while (num_ops--) {

      // gen key/value pair
      int nkey = std::rand() % 100;
      std::string key = tostr(nkey);
      int nval = std::rand() % 100;
      std::string val = tostr(nval);

      // flip coin to insert or remove
      if ((std::rand() % 100) < 50) {
        txn->Put(key, val);
      } else {
        txn->Delete(key);
      }
    }
    txn->Commit();

    // this keeps the snapshot if it isn't a duplicate (ie the txn didn't do
    // anything). this special case isn't bc of the db internals, its because
    // the graphviz generation isn't very smart.
    auto snapshot = db->GetSnapshot();
#ifdef FIXME
    if (snapshot.root != snapshots.back().root)
#endif
      snapshots.push_back(snapshot);
  }

  db->write_dot_history(std::cout, snapshots);

  return 0;
}
