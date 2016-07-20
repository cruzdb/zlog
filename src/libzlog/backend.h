#ifndef LIBZLOG_BACKEND_H
#define LIBZLOG_BACKEND_H

#include <rados/librados.hpp>

namespace zlog {

class Backend {
 public:

  // these must be synchronized with cls_zlog_client.h
  enum {
    CLS_ZLOG_OK            = 0x00,
    CLS_ZLOG_STALE_EPOCH   = 0x01,
    CLS_ZLOG_READ_ONLY     = 0x02,
    CLS_ZLOG_NOT_WRITTEN   = 0x03,
    CLS_ZLOG_INVALIDATED   = 0x04,
    CLS_ZLOG_INVALID_EPOCH = 0x05,
  };

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

  static Backend *CreateV1();
  static Backend *CreateV2();
};

}

#endif