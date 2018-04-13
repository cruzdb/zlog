#include <errno.h>
#include <iostream>
#include "cls_zlog_client.h"
#include "storage/ceph/protobuf_bufferlist_adapter.h"
#include "storage/ceph/cls_zlog.pb.h"

namespace zlog {

void cls_zlog_read(librados::ObjectReadOperation& op, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::ReadEntry call;
  call.set_epoch(epoch);
  call.set_pos(position);
  call.set_stride(stride);
  call.set_max_size(max_size);
  encode(bl, call);
  op.exec("zlog", "entry_read", bl);
}

void cls_zlog_write(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size,
    ceph::bufferlist& data)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::WriteEntry call;
  call.set_epoch(epoch);
  call.set_pos(position);
  call.set_stride(stride);
  call.set_max_size(max_size);
  call.set_data(data.c_str(), data.length());
  encode(bl, call);
  op.exec("zlog", "entry_write", bl);
}

void cls_zlog_invalidate(librados::ObjectWriteOperation& op,
    uint64_t epoch, uint64_t position, uint32_t stride, uint32_t max_size,
    bool force)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::InvalidateEntry call;
  call.set_epoch(epoch);
  call.set_pos(position);
  call.set_force(force);
  call.set_stride(stride);
  call.set_max_size(max_size);
  encode(bl, call);
  op.exec("zlog", "entry_invalidate", bl);
}

void cls_zlog_seal(librados::ObjectWriteOperation& op, uint64_t epoch)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::Seal call;
  call.set_epoch(epoch);
  encode(bl, call);
  op.exec("zlog", "entry_seal", bl);
}

class ClsZlogMaxPositionReply : public librados::ObjectOperationCompletion {
 public:
  ClsZlogMaxPositionReply(uint64_t *pposition, bool *pempty, int *pret) :
    pposition_(pposition), pempty_(pempty), pret_(pret)
  {}

  void handle_completion(int ret, ceph::bufferlist& bl) {
    if (ret == 0) {
      zlog_ceph_proto::MaxPos reply;
      if (decode(bl, &reply)) {
        *pempty_ = !reply.has_pos();
        if (reply.has_pos())
          *pposition_ = reply.pos();
      } else {
        ret = -EIO;
      }
    } if (ret > 0) {
      std::cerr << "unexpected positive rv" << std::endl;
      ret = -EIO;
    }
    *pret_ = ret;
  }

 private:
  uint64_t *pposition_;
  bool *pempty_;
  int *pret_;
};

void cls_zlog_max_position(librados::ObjectReadOperation& op, uint64_t epoch,
    uint64_t *pposition, bool *pempty, int *pret)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::ReadMaxPos call;
  call.set_epoch(epoch);
  encode(bl, call);
  op.exec("zlog", "entry_max_position", bl,
      new ClsZlogMaxPositionReply(pposition, pempty, pret));
}

void cls_zlog_init_head(librados::ObjectWriteOperation& op,
    const std::string& prefix)
{
  zlog_ceph_proto::HeadObjectHeader header;
  header.set_deleted(false);
  header.set_prefix(prefix);
  // don't set max_epoch...
  assert(!header.has_max_epoch());

  ceph::bufferlist bl;
  encode(bl, header);

  op.assert_exists();
  op.setxattr(HEAD_HEADER_KEY, bl);
}

void cls_zlog_create_view(librados::ObjectWriteOperation& op,
    uint64_t epoch, ceph::bufferlist& data)
{
  zlog_ceph_proto::CreateView call;
  call.set_epoch(epoch);
  call.set_data(data.c_str(), data.length());

  ceph::bufferlist bl;
  encode(bl, call);
  op.exec("zlog", "view_create", bl);
}

void cls_zlog_read_view(librados::ObjectReadOperation& op,
    uint64_t epoch, uint32_t max_views)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::ReadView call;
  call.set_epoch(epoch);
  call.set_max_views(max_views);
  encode(bl, call);
  op.exec("zlog", "view_read", bl);
}

}
