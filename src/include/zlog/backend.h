#ifndef ZLOG_INCLUDE_ZLOG_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_BACKEND_H
#include <rados/librados.hpp>

class Backend {
 public:
  explicit Backend(void *ioctx) : ioctx(ioctx) {}
  void *ioctx;

  virtual int CreateHeadObject(const std::string& oid, ceph::bufferlist& bl) = 0;
};

#endif
