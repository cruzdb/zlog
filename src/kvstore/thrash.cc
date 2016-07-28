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

    std::cerr << "############################################" << std::endl;
    std::cerr << "############################################" << std::endl;
    std::cerr << "############################################" << std::endl;

    // num txns
    int num_txns = 20;
    while (num_txns--) {

      // number of operations in this transaction
      int num_ops = std::rand() % 10;

      auto txn = db.BeginTransaction();
      while (num_ops--) {
        // gen key/value pair
        int nkey = std::rand() % 100;
        std::string key = tostr(nkey);
        int nval = std::rand() % 100;
        std::string val = tostr(nval);

        // flip coin to insert or remove
        if ((std::rand() % 100) < 50) {
          std::cout << "-----" << num_txns << "-OPERATION: insert: " << key << " " << val << std::endl;
          truth[key] = val;
          txn.Put(key, val);
        } else {
          std::cout << "-----" << num_txns << "-OPERATION: erase: " << key << std::endl;
          auto it = truth.find(key);
          if (it != truth.end())
            truth.erase(it);
          txn.Delete(key);
        }
      }
      txn.Commit();

      truth_history.push_back(truth);
      db_history.push_back(db.GetSnapshot());
    }

    assert(truth_history.size() == db_history.size());
    for (unsigned i = 0; i < db_history.size(); i++) {
      for (auto it : truth_history[i]) {
        std::cout << "TRUTH-" << i << ": " << it.first << " " << it.second << std::endl;
      }
      for (auto it : db.stl_map(db_history[i])) {
        std::cout << "   DB-" << i << ": " << it.first << " " << it.second << std::endl;
      }
      assert(truth_history[i] == db.stl_map(db_history[i]));
    }
  }

  return 0;
}
