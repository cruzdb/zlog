#pragma once
#include <google/protobuf/message.h>
#include <rados/buffer.h>

static inline void encode(ceph::buffer::list& bl,
    const google::protobuf::Message& msg)
{
  assert(msg.IsInitialized());
  char buf[msg.ByteSize()];
  assert(msg.SerializeToArray(buf, sizeof(buf)));
  bl.append(buf, sizeof(buf));
}

static inline bool decode(ceph::bufferlist& bl,
    google::protobuf::Message* msg)
{
  if (!msg->ParseFromArray(bl.c_str(), bl.length())) {
    return false;
  }
  if (!msg->IsInitialized()) {
    return false;
  }
  return true;
}
