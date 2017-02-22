#include <errno.h>
#include <iostream>
#include "cls_zlog_client.h"
#include "zlog.pb.h"

void encode(ceph::buffer::list& bl, google::protobuf::Message& msg) {
  assert(msg.IsInitialized());
  char buf[msg.ByteSize()];
  assert(msg.SerializeToArray(buf, sizeof(buf)));
  bl.append(buf, sizeof(buf));
}

bool decode(ceph::bufferlist& bl, google::protobuf::Message* msg) {
  if (bl.length() == 0) {
    return false;
  }
  if (!msg->ParseFromString(bl.to_str())) {
    std::cerr << "decode: unable to decode message" << std::endl;
    return false;
  }
  if (!msg->IsInitialized()) {
    std::cerr << "decode: message is uninitialized" << std::endl;
    return false;
  }
  return true;
}

namespace zlog {

void cls_zlog_seal(librados::ObjectWriteOperation& op, uint64_t epoch)
{
  ceph::bufferlist in;
  zlog_ceph_proto::SealOp call;
  call.set_epoch(epoch);
  encode(in, call);
  op.exec("zlog", "seal", in);
}

void cls_zlog_fill(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position)
{
  ceph::bufferlist in;
  zlog_ceph_proto::FillOp call;
  call.set_epoch(epoch);
  call.set_pos(position);
  encode(in, call);
  op.exec("zlog", "fill", in);
}

void cls_zlog_write(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position, ceph::bufferlist& data)
{
  ceph::bufferlist in;
  zlog_ceph_proto::WriteOp call;
  call.set_epoch(epoch);
  call.set_pos(position);
  call.set_data(data.to_str());
  encode(in, call);
  op.exec("zlog", "write", in);
}

void cls_zlog_read(librados::ObjectReadOperation& op, uint64_t epoch,
    uint64_t position)
{
  ceph::bufferlist in;
  zlog_ceph_proto::ReadOp call;
  call.set_epoch(epoch);
  call.set_pos(position);
  encode(in, call);
  op.exec("zlog", "read", in);
}

void cls_zlog_trim(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position)
{
  ceph::bufferlist in;
  zlog_ceph_proto::TrimOp call;
  call.set_epoch(epoch);
  call.set_pos(position);
  encode(in, call);
  op.exec("zlog", "trim", in);
}

class ClsZlogMaxPositionReply : public librados::ObjectOperationCompletion {
 public:
  ClsZlogMaxPositionReply(uint64_t *pposition, int *pret) :
    pposition_(pposition), pret_(pret)
  {}

  void handle_completion(int ret, ceph::bufferlist& outbl) {
    if (ret == CLS_ZLOG_OK) {
      zlog_ceph_proto::MaxPositionRet reply;
      if (decode(outbl, &reply)) {
        *pposition_ = reply.pos();
      } else {
        ret = -EIO;
      }
    }
    *pret_ = ret;
  }

 private:
  uint64_t *pposition_;
  int *pret_;
};

void cls_zlog_max_position(librados::ObjectReadOperation& op, uint64_t epoch,
    uint64_t *pposition, int *pret)
{
  ceph::bufferlist in;
  zlog_ceph_proto::MaxPositionOp call;
  call.set_epoch(epoch);
  encode(in, call);
  op.exec("zlog", "max_position", in, new ClsZlogMaxPositionReply(pposition, pret));
}

void cls_zlog_seal_v2(librados::ObjectWriteOperation& op, uint64_t epoch)
{
  ceph::bufferlist in;
  zlog_ceph_proto::SealOp call;
  call.set_epoch(epoch);
  encode(in, call);
  op.exec("zlog", "seal_v2", in);
}

void cls_zlog_fill_v2(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position)
{
  ceph::bufferlist in;
  zlog_ceph_proto::FillOp call;
  call.set_epoch(epoch);
  call.set_pos(position);
  encode(in, call);
  op.exec("zlog", "fill_v2", in);
}

void cls_zlog_write_v2(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position, ceph::bufferlist& data)
{
  ceph::bufferlist in;
  zlog_ceph_proto::WriteOp call;
  call.set_epoch(epoch);
  call.set_pos(position);
  call.set_data(data.to_str());
  encode(in, call);
  op.exec("zlog", "write_v2", in);
}

void cls_zlog_read_v2(librados::ObjectReadOperation& op, uint64_t epoch,
    uint64_t position)
{
  ceph::bufferlist in;
  zlog_ceph_proto::ReadOp call;
  call.set_epoch(epoch);
  call.set_pos(position);
  encode(in, call);
  op.exec("zlog", "read_v2", in);
}

void cls_zlog_trim_v2(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position)
{
  ceph::bufferlist in;
  zlog_ceph_proto::TrimOp call;
  call.set_epoch(epoch);
  call.set_pos(position);
  encode(in, call);
  op.exec("zlog", "trim_v2", in);
}

void cls_zlog_max_position_v2(librados::ObjectReadOperation& op, uint64_t epoch,
    uint64_t *pposition, int *pret)
{
  ceph::bufferlist in;
  zlog_ceph_proto::MaxPositionOp call;
  call.set_epoch(epoch);
  encode(in, call);
  op.exec("zlog", "max_position_v2", in, new ClsZlogMaxPositionReply(pposition, pret));
}

void cls_zlog_set_projection(librados::ObjectWriteOperation& op,
    uint64_t epoch, ceph::bufferlist& data)
{
  ceph::bufferlist inbl;
  zlog_ceph_proto::SetProjectionOp call;
  call.set_epoch(epoch);
  call.set_data(data.to_str());
  encode(inbl, call);
  op.exec("zlog", "set_projection", inbl);
}

class GetProjectionReply : public librados::ObjectOperationCompletion {
 public:
  GetProjectionReply(int *pret, uint64_t *pepoch, ceph::bufferlist *out) :
    pret_(pret), pepoch_(pepoch), out_(out)
  {}

  void handle_completion(int ret, ceph::bufferlist& outbl) {
    if (ret == 0) {
      zlog_ceph_proto::GetProjectionRet reply;
      if (decode(outbl, &reply)) {
        if (pepoch_)
          *pepoch_ = reply.epoch();
        out_->append(reply.out());
      } else {
        ret = -EIO;
      }
    }
    *pret_ = ret;
  }

 private:
  int *pret_;
  uint64_t *pepoch_;
  ceph::bufferlist *out_;
};

static void __get_projection(librados::ObjectReadOperation& op,
    uint64_t epoch, bool latest, int *pret, uint64_t *pepoch, ceph::bufferlist *out)
{
  ceph::bufferlist inbl;
  zlog_ceph_proto::GetProjectionOp call;
  call.set_epoch(epoch);
  call.set_latest(latest);
  encode(inbl, call);
  op.exec("zlog", "get_projection", inbl,
      new GetProjectionReply(pret, pepoch, out));
}

void cls_zlog_get_latest_projection(librados::ObjectReadOperation& op,
    int *pret, uint64_t *pepoch, ceph::bufferlist *out)
{
  __get_projection(op, 0, true, pret, pepoch, out);
}

void cls_zlog_get_projection(librados::ObjectReadOperation& op, int *pret,
    uint64_t epoch, ceph::bufferlist *out)
{
  __get_projection(op, epoch, false, pret, NULL, out);
}

}
