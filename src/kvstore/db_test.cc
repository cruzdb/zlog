#include "db.h"
#include <sstream>
#include <iomanip>

static inline std::string tostr(int value)
{
  std::stringstream ss;
  ss << std::setw(3) << std::setfill('0') << value;
  return ss.str();
}

static std::map<std::string, std::string> get_map(DB& db,
    Snapshot snapshot, bool forward)
{
  std::map<std::string, std::string> map;
  auto it = db.NewIterator(snapshot);
  if (forward) {
    it.SeekToFirst();
    while (it.Valid()) {
      map[it.key()] = it.value();
      it.Next();
    }
  } else {
    it.SeekToLast();
    while (it.Valid()) {
      map[it.key()] = it.value();
      it.Prev();
    }
  }
  return map;
}

int main(int argc, char **argv)
{
  std::srand(0);

  while (1) {
    // truth and ptree history
    std::vector<std::map<std::string, std::string>> truth_history;

    // initially empty truth
    std::map<std::string, std::string> truth;
    truth_history.push_back(truth);

    // initially empty ptree
    VectorBackend be;
    DB db;
    int ret = db.Open(&be, true);
    assert(ret == 0);

    std::vector<Snapshot> db_history;
    db_history.push_back(db.GetSnapshot());

    for (int i = 0; i < 300; i++) {

      int nkey = std::rand() % 100;
      std::string key = tostr(nkey);

      int nval = std::rand() % 100;
      std::string val = tostr(nval);

      // update truth and save snapshot
      truth[key] = val;
      truth_history.push_back(truth);

      // update tree and save snapshot
      auto txn = db.BeginTransaction();
      txn.Put(key, val);
      txn.Commit();

      db_history.push_back(db.GetSnapshot());
    }

    assert(truth_history.size() == db_history.size());

    for (unsigned i = 0; i < db_history.size(); i++) {
      assert(truth_history[i] == get_map(db, db_history[i], true));
      assert(truth_history[i] == get_map(db, db_history[i], false));
    }
  }

  return 0;
}
