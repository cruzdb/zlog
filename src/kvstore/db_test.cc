#include "ptree.h"

int main(int argc, char **argv)
{
  // this is the database "log"
  std::vector<std::string> db;

  // build a tree. each insert will append a delta to the database log. after
  // we construct the tree we'll compare it to a tree constructed by reading
  // from the log database.
  PTree<int> tree(&db);
  for (int i = 0; i < 5; i++) {
    int val = std::rand();
    tree = tree.insert(val);
  }

#if 1
  PTree<int> tree_restored(&db);
  tree_restored.restore();

  assert(tree.stl_set() == tree_restored.stl_set());
#endif
  return 0;
}
