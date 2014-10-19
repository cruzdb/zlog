#ifndef SKYTYPE_H
#define SKYTYPE_H

#include "../contrail/contrail.h"

namespace skytype {
  class SkyObject {
    public:
      explicit SkyObject(contrail::Log& log) : log_(log), position_(0) {}

    protected:
      virtual void apply(const void *data) = 0;
      int update_helper(const void *data, size_t size);
      int query_helper();

    private:
      contrail::Log& log_;
      uint64_t position_;
  };
}

#endif
