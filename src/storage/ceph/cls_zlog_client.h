#pragma once
#include <rados/librados.hpp>

// namespace for head object (sync with cls_zlog)
#define HEAD_HEADER_KEY "zlog.head.header"

namespace zlog {

  void cls_zlog_read(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size);

  void cls_zlog_write(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      ceph::bufferlist& data);

  void cls_zlog_invalidate(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size, bool force);

  void cls_zlog_seal(librados::ObjectWriteOperation& op, uint64_t epoch);

  void cls_zlog_max_position(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t *pposition, bool *pempty, int *pret);

  void cls_zlog_init_head(librados::ObjectWriteOperation& op,
      const std::string& prefix);

  void cls_zlog_read_view(librados::ObjectReadOperation& op,
      uint64_t epoch, uint32_t max_views = 100);

  void cls_zlog_create_view(librados::ObjectWriteOperation& op,
      uint64_t epoch, ceph::bufferlist& bl);
}
