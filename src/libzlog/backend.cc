#include "backend.h"

#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>

using namespace zlog;

class BackendV1 : public TmpBackend {
 public:
  void seal(librados::ObjectWriteOperation& op, uint64_t epoch) {
    cls_zlog_seal(op, epoch);
  }

  void fill(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position) {
    cls_zlog_fill(op, epoch, position);
  }

  void write(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position, ceph::bufferlist& data) {
    cls_zlog_write(op, epoch, position, data);
  }

  void read(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t position) {
    cls_zlog_read(op, epoch, position);
  }

  void trim(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position) {
    cls_zlog_trim(op, epoch, position);
  }

  void max_position(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t *pposition, int *pret) {
    cls_zlog_max_position(op, epoch, pposition, pret);
  }
};

class BackendV2 : public TmpBackend {
 public:
  void seal(librados::ObjectWriteOperation& op, uint64_t epoch) {
    cls_zlog_seal_v2(op, epoch);
  }

  void fill(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position) {
    cls_zlog_fill_v2(op, epoch, position);
  }

  void write(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position, ceph::bufferlist& data) {
    cls_zlog_write_v2(op, epoch, position, data);
  }

  void read(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t position) {
    cls_zlog_read_v2(op, epoch, position);
  }

  void trim(librados::ObjectWriteOperation& op, uint64_t epoch,
      uint64_t position) {
    cls_zlog_trim_v2(op, epoch, position);
  }

  void max_position(librados::ObjectReadOperation& op, uint64_t epoch,
      uint64_t *pposition, int *pret) {
    cls_zlog_max_position_v2(op, epoch, pposition, pret);
  }
};

void TmpBackend::set_projection(librados::ObjectWriteOperation& op,
    uint64_t epoch, ceph::bufferlist& data)
{
  cls_zlog_set_projection(op, epoch, data);
}

void TmpBackend::get_latest_projection(librados::ObjectReadOperation& op,
    int *pret, uint64_t *pepoch, ceph::bufferlist *out)
{
  cls_zlog_get_latest_projection(op, pret, pepoch, out);
}

void TmpBackend::get_projection(librados::ObjectReadOperation& op,
      int *pret, uint64_t epoch, ceph::bufferlist *out)
{
  cls_zlog_get_projection(op, pret, epoch, out);
}

TmpBackend *TmpBackend::CreateV1()
{
  return new BackendV1();
}

TmpBackend *TmpBackend::CreateV2()
{
  return new BackendV2();
}
