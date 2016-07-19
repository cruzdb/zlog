#include "ptree.h"

int main(int argc, char **argv)
{
  std::vector<std::string> db;
  PTree<int> tree(&db);

  std::vector<PTree<int>> versions;
  for (int i = 0; i < 5; i++) {
    int val = std::rand() % 200;
    tree = tree.insert(val);
    tree.validate_rb_tree();
    std::cerr << val << std::endl;
    versions.push_back(tree);
  }

  //tree.write_dot(std::cout, true)
  tree.write_dot(std::cout, versions);

  return 0;
}
