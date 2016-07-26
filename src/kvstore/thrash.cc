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
  while (1) {
    std::vector<std::set<std::string>> truth_history;
    std::set<std::string> truth;
    truth_history.push_back(truth);

    DB db;

    std::vector<Snapshot> db_history;
    db_history.push_back(db.GetSnapshot());

    for (int i = 0; i < 500; i++) {
      int nval = std::rand();
      std::string val = tostr(nval);

      truth.insert(val);
      truth_history.push_back(truth);

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
  }

  return 0;
}
