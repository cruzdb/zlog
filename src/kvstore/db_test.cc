#include "ptree.h"
#include <sstream>

int main(int argc, char **argv)
{
  std::srand(0);
  while (1) {

  // database log history
  std::vector<std::string> db;

  // truth and ptree history
  std::vector<std::set<std::string>> truth_history;
  std::vector<PTree> tree_history;

  // initially empty truth
  std::set<std::string> truth;
  truth_history.push_back(truth);

  // initially empty ptree
  PTree tree(&db);
  tree_history.push_back(tree);

  for (int i = 0; i < 200; i++) {
    int val = std::rand();
    std::stringstream ss;
    ss << val;

    // update truth and save snapshot
    truth.insert(ss.str());
    truth_history.push_back(truth);

    // update tree and save snapshot
    tree = tree.insert(ss.str());
    tree_history.push_back(tree);
  }

  assert(truth_history.size() == tree_history.size());
  assert(db.size() == truth_history.size());

  // each of the truth and tree history snapshot points match
  for (unsigned i = 0; i < truth_history.size(); i++) {
    assert(tree_history[i].validate_rb_tree());
    assert(truth_history[i] == tree_history[i].stl_set());
  }

  // each of the truths match the tree if we deserialize it
  for (unsigned i = 0; i < truth_history.size(); i++) {
    PTree tree_restored(NULL);
    tree_restored.restore(&db, i);
    assert(truth_history[i] == tree_restored.stl_set());
  }

  // and it works in reverse
  for (int i = truth_history.size() - 1; i >= 0; i--) {
    PTree tree_restored(NULL);
    tree_restored.restore(&db, i);
    assert(truth_history[i] == tree_restored.stl_set());
  }

  // and some random access
  for (int x = 0; x < std::min(100, (int)truth_history.size()); x++) {
    int i = std::rand() % truth_history.size();
    PTree tree_restored(NULL);
    tree_restored.restore(&db, i);
    assert(truth_history[i] == tree_restored.stl_set());
  }
  }

  return 0;
}
