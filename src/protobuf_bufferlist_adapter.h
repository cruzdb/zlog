/*
 * TODO;
 *  - implement zero-copy adapter
 */
#ifndef PROTOBUF_BUFFERLIST_ADAPTER
#define PROTOBUF_BUFFERLIST_ADAPTER

#include <iostream>
#include <rados/buffer.h>

/*
 * Pack a protobuf message into a bufferlist.
 */
template<typename T>
void pack_msg(ceph::bufferlist& bl, T& m) {
  assert(m.IsInitialized());
  char buf[m.ByteSize()];
  assert(m.SerializeToArray(buf, sizeof(buf)));
  bl.append(buf, sizeof(buf));
}

/*
 * Pack a protobuf message into a bufferlist with a length header.
 */
template<typename T>
void pack_msg_hdr(ceph::bufferlist& bl, T& m) {
  assert(m.IsInitialized());
  uint32_t buf_size = m.ByteSize();
  char buf[buf_size];
  assert(m.SerializeToArray(buf, buf_size));
  uint32_t be_buf_size = htonl(buf_size);
  bl.append((char*)&be_buf_size, sizeof(be_buf_size));
  bl.append(buf, sizeof(buf));
}

/*
 * Unpack a protobuf message from a bufferlist.
 */
template<typename T>
bool unpack_msg(T& m, ceph::bufferlist& bl) {
  if (!m.ParseFromArray(bl.c_str(), bl.length())) {
    std::cerr << "unpack_msg: could not parse message" << std::endl;
    return false;
  }
  if (!m.IsInitialized()) {
    std::cerr << "unpack_msg: message is uninitialized" << std::endl;
    return false;
  }
  return true;
}

#endif
