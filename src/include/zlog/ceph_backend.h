#ifndef ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#include <rados/librados.hpp>
#include "zlog/backend.h"

class CephBackend : public Backend {
 public:
  explicit CephBackend(librados::IoCtx *ioctx) : Backend(ioctx) {}
};

#endif
