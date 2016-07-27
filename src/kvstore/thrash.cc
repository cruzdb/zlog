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

  for (int i = 0; i < 10; i++) {
    std::vector<std::set<std::string>> truth_history;
    std::set<std::string> truth;
    truth_history.push_back(truth);

    DB db;

    std::vector<Snapshot> db_history;
    db_history.push_back(db.GetSnapshot());

    // how many transactions
    for (int i = 0; i < 100; i++) {

      // number of operations in this transaction
      int num_ops = std::rand() % 10;

      auto txn = db.BeginTransaction();
      for (int i = 0; i < num_ops; i++) {
        int nval = std::rand() % 500;
        std::string val = tostr(nval);
        if ((std::rand() % 100) < 50) {
          std::cout << "operation: insert: " << val << std::endl;
          truth.insert(val);
          txn.Put(val);
        } else {
          std::cout << "operation: erase: " << val << std::endl;
          truth.erase(val);
          txn.Delete(val);
        }
      }
      txn.Commit();

      truth_history.push_back(truth);
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
