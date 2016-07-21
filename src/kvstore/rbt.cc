#include "ptree.h"
#include <sstream>

int main(int argc, char **argv)
{
  std::vector<std::string> db;
  PTree tree(&db);

  std::vector<PTree> versions;
  for (int i = 0; i < 5; i++) {
    int val = std::rand() % 200;
    std::stringstream ss;
    ss << val;
    tree = tree.insert(ss.str());
    tree.validate_rb_tree();
    std::cerr << val << std::endl;
    versions.push_back(tree);
  }

  //tree.write_dot(std::cout, true)
  tree.write_dot(std::cout, versions);

  return 0;
}
