#ifndef ZLOG_INCLUDE_ZLOG_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_BACKEND_H
#include <rados/librados.hpp>

class Backend {
 public:
  explicit Backend(void *ioctx) : ioctx(ioctx) {}
  void *ioctx;

  virtual int CreateHeadObject(const std::string& oid, ceph::bufferlist& bl) = 0;

  /*
   *
   */
  virtual int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position) = 0;

  /*
   *
   */
  virtual int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data) = 0;

  /*
   *
   */
  virtual int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position) = 0;

  /*
   *
   */
  virtual int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position) = 0;
};

#endif
