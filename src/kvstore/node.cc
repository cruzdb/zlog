#include "db_impl.h"

NodeRef NodePtr::fetch(std::vector<std::pair<int64_t, int>>& trace)
{
  assert(db_);
  return db_->fetch(trace, csn_, offset_);
}
