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

  for (int i = 0; i < 30; i++) {
    int nval = std::rand() % 1000;
    std::string val = tostr(nval);
    db.insert(val);
  }

  db.write_dot_history(std::cout);

  return 0;
}
