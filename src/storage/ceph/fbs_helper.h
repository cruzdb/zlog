#pragma once
#include <rados/buffer.h>
#include "storage/ceph/cls_zlog_generated.h"

template<typename T>
static inline const T* fbs_bl_decode(ceph::bufferlist *bl)
{
  const uint8_t *data = (const uint8_t*)bl->c_str();
  const size_t len = bl->length();
  flatbuffers::Verifier verifier(data, len);
  if (!verifier.VerifyBuffer<T>(nullptr)) {
    return nullptr;
  }
  return flatbuffers::GetRoot<T>(data);
}

static inline void fbs_bl_encode(flatbuffers::FlatBufferBuilder& fbb,
    ceph::bufferlist *bl)
{
  const auto buf = (char*)fbb.GetBufferPointer();
  const auto size = fbb.GetSize();
  bl->append(buf, size);
}
