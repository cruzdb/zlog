#include "db_impl.h"

NodeRef NodePtr::fetch()
{
  assert(db_);
  //std::cout << "NodePtr::fetch: " << csn_ << "/" << offset_ << std::endl;
  return db_->fetch(csn_, offset_);
}
