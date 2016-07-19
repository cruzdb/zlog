#include "ptree.h"

int main(int argc, char **argv)
{
  while (1) {
    std::vector<std::set<int>> truth_history;
    std::set<int> truth;
    truth_history.push_back(truth);

    std::vector<PTree<int>> tree_history;
    std::vector<std::string> db;
    PTree<int> tree(&db);
    tree_history.push_back(tree);

    for (int i = 0; i < 10000; i++) {
      int val = std::rand();

      truth.insert(val);
      truth_history.push_back(truth);

      tree = tree.insert(val);
      tree_history.push_back(tree);
    }

    assert(truth_history.size() == tree_history.size());
    for (unsigned i = 0; i < truth_history.size(); i++) {
      assert(tree_history[i].validate_rb_tree());
      assert(truth_history[i] == tree_history[i].stl_set());
    }
  }

  return 0;
}
