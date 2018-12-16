#include <errno.h>
#include <iostream>
#include "cls_zlog_client.h"
#include "storage/ceph/protobuf_bufferlist_adapter.h"
#include "storage/ceph/cls_zlog.pb.h"

namespace zlog {

void cls_zlog_read(librados::ObjectReadOperation& op, uint64_t epoch,
    uint64_t position)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::ReadEntry call;
  call.set_epoch(epoch);
  call.set_pos(position);
  encode(bl, call);
  op.exec("zlog", "entry_read", bl);
}

void cls_zlog_write(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position, ceph::bufferlist& data)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::WriteEntry call;
  call.set_epoch(epoch);
  call.set_pos(position);
  call.set_data(data.c_str(), data.length());
  encode(bl, call);
  op.exec("zlog", "entry_write", bl);
}

void cls_zlog_invalidate(librados::ObjectWriteOperation& op,
    uint64_t epoch, uint64_t position, bool force)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::InvalidateEntry call;
  call.set_epoch(epoch);
  call.set_pos(position);
  call.set_force(force);
  encode(bl, call);
  op.exec("zlog", "entry_invalidate", bl);
}

void cls_zlog_seal(librados::ObjectWriteOperation& op, uint64_t epoch,
    boost::optional<uint32_t> omap_max_size)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::Seal call;
  call.set_epoch(epoch);
  if (omap_max_size) {
    call.set_omap_max_size(*omap_max_size);
  } else {
    call.set_omap_max_size(-1);
  }
  encode(bl, call);
  op.exec("zlog", "entry_seal", bl);
}

void cls_zlog_max_position(librados::ObjectReadOperation& op, uint64_t epoch)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::ReadMaxPos call;
  call.set_epoch(epoch);
  encode(bl, call);
  op.exec("zlog", "entry_max_position", bl);
}

void cls_zlog_init_head(librados::ObjectWriteOperation& op,
    const std::string& prefix)
{
  zlog_ceph_proto::InitHead call;
  call.set_prefix(prefix);

  ceph::bufferlist bl;
  encode(bl, call);
  op.exec("zlog", "head_init", bl);
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

void cls_zlog_read_unique_id(librados::ObjectReadOperation& op)
{
  ceph::bufferlist bl;
  op.exec("zlog", "unique_id_read", bl);
}

void cls_zlog_write_unique_id(librados::ObjectWriteOperation& op, uint64_t id)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::UniqueId call;
  call.set_id(id);
  encode(bl, call);
  op.exec("zlog", "unique_id_write", bl);
}

}
