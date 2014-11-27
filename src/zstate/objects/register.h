#ifndef SKYTYPE_REGISTER_H
#define SKYTYPE_REGISTER_H

#include <errno.h>
#include "libzlog.h"
#include "zstate/skytype.h"

class Register : private skytype::SkyObject {
  public:
    Register(zlog::Log& log) : SkyObject(log), state_(0) {}

    int read(int *value) {
      int ret = query_helper();
      if (ret)
        return ret;
      *value = state_;
      return 0;
    }

    int write(int value) {
      return update_helper(&value, sizeof(int));
    }

  private:
    int state_;

    void apply(const void *data) {
      state_ = *(int*)data;
    }
};

#endif
