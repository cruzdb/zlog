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

  auto it = db.NewIterator();
  assert(!it.Valid());

  it.SeekToFirst();
  assert(!it.Valid());

  it.SeekToLast();
  assert(!it.Valid());

  std::vector<std::string> strs{"a", "b", "c"};
  for (auto s : strs) {
    auto txn = db.BeginTransaction();
    txn.Put(s, "");
    txn.Commit();
  }

  auto it2 = db.NewIterator();
  assert(!it2.Valid());

#if 0
  it2.SeekToFirst();
  while (it2.Valid()) {
    std::cout << it2.key() << std::endl;
    it2.Next();
  }
#endif

  // not working....
  it2.SeekToLast();
  while (it2.Valid()) {
    std::cout << it2.key() << std::endl;
    it2.Next();
  }

  return 0;
}
