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
  DB db;

  std::vector<Snapshot> snapshots;
  snapshots.push_back(db.GetSnapshot());

  // how many transactions
  for (int i = 0; i < 5; i++) {
    // number of operations in this transaction
    int num_ops = std::rand() % 5 + 1;

    auto txn = db.BeginTransaction();
    for (int i = 0; i < num_ops; i++) {
      int nval = std::rand() % 20;
      std::string val = tostr(nval);
      if ((std::rand() % 100) < 80) {
        std::cerr << "operation: insert: " << val << std::endl;
        txn.Put(val);
      } else {
        std::cerr << "operation: erase: " << val << std::endl;
        txn.Delete(val);
      }
    }
    txn.Commit();
    snapshots.push_back(db.GetSnapshot());
  }

  db.write_dot_history(std::cout, snapshots);

  return 0;
}
