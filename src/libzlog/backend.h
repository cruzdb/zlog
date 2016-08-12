#ifndef LIBZLOG_BACKEND_H
#define LIBZLOG_BACKEND_H

#include <rados/librados.hpp>

namespace zlog {

class TmpBackend {
 public:

  // object class interface

  virtual void seal(librados::ObjectWriteOperation& op, uint64_t epoch) = 0;

  virtual void fill(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position) = 0;

  virtual void write(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position, ceph::bufferlist& data) = 0;

  virtual void read(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t position) = 0;

  virtual void trim(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position) = 0;

  virtual void max_position(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t *pposition, int *pret) = 0;

  // projection management

  static void set_projection(librados::ObjectWriteOperation& op,
      uint64_t epoch, ceph::bufferlist& data);

  static void get_latest_projection(librados::ObjectReadOperation& op,
      int *pret, uint64_t *pepoch, ceph::bufferlist *out);

  static void get_projection(librados::ObjectReadOperation& op,
      int *pret, uint64_t epoch, ceph::bufferlist *out);

  static TmpBackend *CreateV1();
  static TmpBackend *CreateV2();
};

}

#endif
