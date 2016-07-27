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

  {
    auto txn = db.BeginTransaction();
    txn.Put(tostr(76));
    txn.Commit();
  }

  {
    auto txn = db.BeginTransaction();
    txn.Delete(tostr(76));
    txn.Commit();
  }


#if 0
  for (int i = 0; i < 30; i++) {
    // generate value
    int nval = std::rand() % 1000;
    std::string val = tostr(nval);

    // run txn
    auto txn = db.BeginTransaction();
    txn.Put(val);
    txn.Commit();
  }
#endif

  db.write_dot_history(std::cout);

  return 0;
}
