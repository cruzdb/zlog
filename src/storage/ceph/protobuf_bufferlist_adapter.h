#pragma once
#include <google/protobuf/message.h>
#include <rados/buffer.h>
#include <iostream>

static inline void encode(ceph::buffer::list& bl,
    const google::protobuf::Message& msg)
{
  assert(msg.IsInitialized());
  char buf[msg.ByteSize()];
  if (!msg.SerializeToArray(buf, sizeof(buf))) {
    std::cout << "failed to serialize" << std::endl << std::flush;
    exit(1);
  }
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
