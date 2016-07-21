#include "ptree.h"
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

    PTree db;

    for (int i = 0; i < 10000; i++) {
      int nval = std::rand();
      std::string val = tostr(nval);

      truth.insert(val);
      truth_history.push_back(truth);

      db.insert(val);
    }

    db.validate_rb_tree(true);
    assert(truth_history.size() == db.num_roots());
    for (unsigned i = 0; i < truth_history.size(); i++) {
      assert(truth_history[i] == db.stl_set(i));
    }
  }

  return 0;
}
