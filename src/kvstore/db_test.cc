#include "db.h"
#include <sstream>
#include <iomanip>

static inline std::string tostr(int value)
{
  std::stringstream ss;
  ss << std::setw(3) << std::setfill('0') << value;
  return ss.str();
}

int main(int argc, char **argv)
{
  std::srand(0);

  while (1) {
    // truth and ptree history
    std::vector<std::set<std::string>> truth_history;

    // initially empty truth
    std::set<std::string> truth;
    truth_history.push_back(truth);

    // initially empty ptree
    DB db;

    std::vector<Snapshot> db_history;
    db_history.push_back(db.GetSnapshot());

    for (int i = 0; i < 300; i++) {
      int nval = std::rand();
      std::string val = tostr(nval);

      // update truth and save snapshot
      truth.insert(val);
      truth_history.push_back(truth);

      // update tree and save snapshot
      auto txn = db.BeginTransaction();
      txn.Put(val);
      txn.Commit();

      db_history.push_back(db.GetSnapshot());
    }

    db.validate_rb_tree(true);

    assert(truth_history.size() == db_history.size());

    for (unsigned i = 0; i < db_history.size(); i++) {
      assert(truth_history[i] == db.stl_set(db_history[i]));
    }

    // each of the truths match the tree if we deserialize it
    for (unsigned i = 0; i < truth_history.size(); i++) {
      DB db2(db.get_db());
      assert(truth_history[i] == db.stl_set(db_history[i]));
    }

    // and it works in reverse
    for (int i = truth_history.size() - 1; i >= 0; i--) {
      DB db2(db.get_db());
      assert(truth_history[i] == db.stl_set(db_history[i]));
    }

    // and some random access
    for (int x = 0; x < std::min(100, (int)truth_history.size()); x++) {
      DB db2(db.get_db());
      int i = std::rand() % truth_history.size();
      assert(truth_history[i] == db.stl_set(db_history[i]));
    }
  }

  return 0;
}
