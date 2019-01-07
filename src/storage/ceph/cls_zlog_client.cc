#include <errno.h>
#include <iostream>
#include "cls_zlog_client.h"
#include "storage/ceph/cls_zlog_generated.h"
#include "fbs_helper.h"

namespace cls_zlog_client {

void cls_zlog_read(librados::ObjectReadOperation& op, uint64_t epoch,
    uint64_t position)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto call = cls_zlog::fbs::CreateReadEntryOp(fbb, epoch, position);
  fbb.Finish(call);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  op.exec("zlog", "entry_read", bl);
}

void cls_zlog_write(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position, ceph::bufferlist& data)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto data_vec = fbb.CreateVector((uint8_t*)data.c_str(), data.length());
  auto call = cls_zlog::fbs::CreateWriteEntryOp(fbb, epoch, position, data_vec);
  fbb.Finish(call);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  op.exec("zlog", "entry_write", bl);
}

void cls_zlog_invalidate(librados::ObjectWriteOperation& op,
    uint64_t epoch, uint64_t position, bool force)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto call = cls_zlog::fbs::CreateInvalidateEntryOp(fbb,
      epoch, position, force);
  fbb.Finish(call);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  op.exec("zlog", "entry_invalidate", bl);
}

void cls_zlog_seal(librados::ObjectWriteOperation& op, uint64_t epoch,
    boost::optional<uint32_t> omap_max_size)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto call = cls_zlog::fbs::CreateSealOp(fbb,
      epoch,
      (omap_max_size ? *omap_max_size : -1));
  fbb.Finish(call);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  op.exec("zlog", "entry_seal", bl);
}

void cls_zlog_max_position(librados::ObjectReadOperation& op, uint64_t epoch)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto call = cls_zlog::fbs::CreateReadMaxPosOp(fbb, epoch);
  fbb.Finish(call);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  op.exec("zlog", "entry_max_position", bl);
}

void cls_zlog_init_head(librados::ObjectWriteOperation& op,
    const std::string& prefix)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto call = cls_zlog::fbs::CreateInitHeadOpDirect(fbb, prefix.c_str());
  fbb.Finish(call);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  op.exec("zlog", "head_init", bl);
}

void cls_zlog_create_view(librados::ObjectWriteOperation& op,
    uint64_t epoch, ceph::bufferlist& data)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto data_vec = fbb.CreateVector((uint8_t*)data.c_str(), data.length());
  auto call = cls_zlog::fbs::CreateCreateViewOp(fbb, epoch, data_vec);
  fbb.Finish(call);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  op.exec("zlog", "view_create", bl);
}

void cls_zlog_read_view(librados::ObjectReadOperation& op,
    uint64_t epoch, uint32_t max_views)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto call = cls_zlog::fbs::CreateReadViewsOp(fbb, epoch, max_views);
  fbb.Finish(call);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  op.exec("zlog", "view_read", bl);
}

void cls_zlog_read_unique_id(librados::ObjectReadOperation& op)
{
  ceph::bufferlist bl;
  op.exec("zlog", "unique_id_read", bl);
}

void cls_zlog_write_unique_id(librados::ObjectWriteOperation& op, uint64_t id)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto call = cls_zlog::fbs::CreateUniqueId(fbb, id);
  fbb.Finish(call);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  op.exec("zlog", "unique_id_write", bl);
}

}
