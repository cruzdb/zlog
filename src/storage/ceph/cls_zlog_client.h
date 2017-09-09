#ifndef CLS_ZLOG_CLIENT_H
#define CLS_ZLOG_CLIENT_H

#include <rados/librados.hpp>

namespace zlog {

  enum {
    CLS_ZLOG_OK            = 0x00,
    CLS_ZLOG_STALE_EPOCH   = 0x01,
    CLS_ZLOG_READ_ONLY     = 0x02,
    CLS_ZLOG_NOT_WRITTEN   = 0x03,
    CLS_ZLOG_INVALIDATED   = 0x04,
    CLS_ZLOG_INVALID_EPOCH = 0x05,
  };

  // version 1

  void cls_zlog_seal(librados::ObjectWriteOperation& op, uint64_t epoch);

  void cls_zlog_fill(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position);

  void cls_zlog_write(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position, ceph::bufferlist& data);

  void cls_zlog_read(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t position);

  void cls_zlog_trim(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position);

  void cls_zlog_max_position(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t *pposition, bool *pempty, int *pret);

  // projection management

  void cls_zlog_set_projection(librados::ObjectWriteOperation& op,
      uint64_t epoch, ceph::bufferlist& data);

  void cls_zlog_get_latest_projection(librados::ObjectReadOperation& op,
      int *pret, uint64_t *pepoch, ceph::bufferlist *out);

  void cls_zlog_get_projection(librados::ObjectReadOperation& op,
      int *pret, uint64_t epoch, ceph::bufferlist *out);

  void cls_zlog_create_view(librados::ObjectWriteOperation& op,
      uint64_t epoch, ceph::bufferlist& bl);

  void cls_zlog_read_view(librados::ObjectReadOperation& op,
      uint64_t epoch);
}

#endif
