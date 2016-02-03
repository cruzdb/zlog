#ifndef ZLOG_INCLUDE_ZLOG_STREAM_H_
#define ZLOG_INCLUDE_ZLOG_STREAM_H_
#include <vector>
#include <rados/librados.hpp>

namespace zlog {

/*
 * Streaming API
 */
class Stream {
 public:
  virtual ~Stream();
  virtual int Append(ceph::bufferlist& data, uint64_t *pposition = NULL) = 0;
  virtual int ReadNext(ceph::bufferlist& bl, uint64_t *pposition = NULL) = 0;
  virtual int Reset() = 0;
  virtual int Sync() = 0;
  virtual uint64_t Id() const = 0;
  virtual std::vector<uint64_t> History() const = 0;
};

}

#endif
