#include <errno.h>
#include <iostream>
#include "cls_zlog_client.h"
#include "storage/ceph/cls_zlog.pb.h"

void encode(ceph::buffer::list& bl, google::protobuf::Message& msg) {
  assert(msg.IsInitialized());
  char buf[msg.ByteSize()];
  assert(msg.SerializeToArray(buf, sizeof(buf)));
  bl.append(buf, sizeof(buf));
}

bool decode(ceph::bufferlist& bl, google::protobuf::Message* msg) {
  if (!msg->ParseFromArray(bl.c_str(), bl.length())) {
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

void cls_zlog_read(librados::ObjectReadOperation& op, uint64_t epoch,
    uint64_t position)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::ReadEntry call;
  call.set_epoch(epoch);
  call.set_pos(position);
  encode(bl, call);
  op.exec("zlog", "read", bl);
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
  op.exec("zlog", "write", bl);
}

static void invalidate(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position, bool force)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::InvalidateEntry call;
  call.set_epoch(epoch);
  call.set_pos(position);
  call.set_force(force);
  encode(bl, call);
  op.exec("zlog", "invalidate", bl);
}

void cls_zlog_fill(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position)
{
  invalidate(op, epoch, position, false);
}


void cls_zlog_trim(librados::ObjectWriteOperation& op, uint64_t epoch,
    uint64_t position)
{
  invalidate(op, epoch, position, true);
}

void cls_zlog_seal(librados::ObjectWriteOperation& op, uint64_t epoch)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::Seal call;
  call.set_epoch(epoch);
  encode(bl, call);
  op.exec("zlog", "seal", bl);
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
  op.exec("zlog", "max_position", bl,
      new ClsZlogMaxPositionReply(pposition, pempty, pret));
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
    uint64_t epoch)
{
  ceph::bufferlist bl;
  zlog_ceph_proto::ReadView call;
  call.set_epoch(epoch);
  encode(bl, call);
  op.exec("zlog", "view_read", bl);
}

}
