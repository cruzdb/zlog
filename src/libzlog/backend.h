#ifndef LIBZLOG_BACKEND_H
#define LIBZLOG_BACKEND_H

#include <rados/librados.hpp>

namespace zlog {

class TmpBackend {
 public:

  // object class interface

  virtual void write(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position, ceph::bufferlist& data) = 0;

  virtual void read(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t position) = 0;

  // projection management

  static void get_projection(librados::ObjectReadOperation& op,
      int *pret, uint64_t epoch, ceph::bufferlist *out);

  static TmpBackend *CreateV1();
  static TmpBackend *CreateV2();
};

}

#endif
