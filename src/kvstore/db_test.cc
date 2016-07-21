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

    for (int i = 0; i < 1000; i++) {
      int nval = std::rand();
      std::string val = tostr(nval);

      // update truth and save snapshot
      truth.insert(val);
      truth_history.push_back(truth);

      // update tree and save snapshot
      db.insert(val);
    }

    db.validate_rb_tree(true);

    assert(truth_history.size() == db.num_roots());

    // each of the truth and tree history snapshot points match
    for (unsigned i = 0; i < truth_history.size(); i++) {
      assert(truth_history[i] == db.stl_set(i));
    }

    // each of the truths match the tree if we deserialize it
    for (unsigned i = 0; i < truth_history.size(); i++) {
      DB db2;
      db2.restore(db, i);
      assert(truth_history[i] == db2.stl_set());
    }

    // and it works in reverse
    for (int i = truth_history.size() - 1; i >= 0; i--) {
      DB db2;
      db2.restore(db, i);
      assert(truth_history[i] == db2.stl_set());
    }

    // and some random access
    for (int x = 0; x < std::min(100, (int)truth_history.size()); x++) {
      int i = std::rand() % truth_history.size();
      DB db2;
      db2.restore(db, i);
      assert(truth_history[i] == db2.stl_set());
    }
  }

  return 0;
}
