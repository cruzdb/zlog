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
    std::vector<std::map<std::string, std::string>> truth_history;
    std::map<std::string, std::string> truth;
    truth_history.push_back(truth);

    DB db;
    std::vector<Snapshot> db_history;
    db_history.push_back(db.GetSnapshot());

    // number of transactions in tree
    int num_txns = std::rand() % 2000;

    std::cout << "building tree with " <<
      num_txns << " transactions" << std::endl;

    while (num_txns--) {

      // number of operations in this transaction
      int num_ops = std::rand() % 10;

      auto txn = db.BeginTransaction();
      while (num_ops--) {
        // flip coin to insert or remove
        if ((std::rand() % 100) < 75) {
          // gen key/value pair to insert/update
          int nkey = std::rand() % 1000;
          std::string key = tostr(nkey);
          int nval = std::rand() % 1000;
          std::string val = tostr(nval);
          truth[key] = val;
          txn.Put(key, val);
        } else {
          // remove things that are actually in tree
          if (truth.empty())
            continue;
          auto it = truth.begin();
          std::advance(it, std::rand() % truth.size());
          assert(it != truth.end());
          std::string key = it->first;
          truth.erase(it);
          txn.Delete(key);
        }
      }
      txn.Commit();

      truth_history.push_back(truth);
      db_history.push_back(db.GetSnapshot());
    }

    uint64_t count = 0;
    std::cout << "verifying tree...";
    assert(truth_history.size() == db_history.size());
    for (unsigned i = 0; i < db_history.size(); i++) {
      count += truth_history[i].size();
      assert(truth_history[i] == db.stl_map(db_history[i]));
    }
    std::cout << " complete! (" << count << ")" << std::endl;
  }

  return 0;
}
