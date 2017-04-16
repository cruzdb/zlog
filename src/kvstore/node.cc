#include "db_impl.h"

SharedNodeRef NodePtr::fetch(std::vector<std::pair<int64_t, int>>& trace)
{
  assert(db_);
  return db_->fetch(trace, csn_, offset_);
}
