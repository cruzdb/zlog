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
  PTree db;

  for (int i = 0; i < 5; i++) {
    int nval = std::rand() % 200;
    std::string val = tostr(nval);
    db.insert(val);
  }

  db.write_dot_history(std::cout);

  return 0;
}
