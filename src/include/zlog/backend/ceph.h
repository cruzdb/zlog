#ifndef ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#include <rados/librados.hpp>
#include "zlog/backend.h"
#include <iostream>
#include "proto/protobuf_bufferlist_adapter.h"

// v1
class CephBackend : public Backend {
 public:
  explicit CephBackend(librados::IoCtx *ioctx);

  ////
  int CreateLog(const std::string& name,
      const std::string& initial_view) override;

  virtual int OpenLog(const std::string& name,
      std::string& prefix) override;

  int ReadViews(const std::string& hoid, uint64_t epoch,
      std::map<uint64_t, std::string>& views) override;

  int ProposeView(const std::string& hoid,
      uint64_t epoch, const std::string& view) override;

  ////

  virtual std::string pool();

  virtual int Seal(const std::string& oid, uint64_t epoch);

  virtual int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos, bool *empty);

  /*
   *
   */
  virtual int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position);

  /*
   *
   */
  virtual int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data);

  /*
   *
   */
  virtual int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position);

  /*
   *
   */
  virtual int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position);

  virtual int AioWrite(const std::string& oid, uint64_t epoch,
      uint64_t position, const Slice& data, void *arg,
      std::function<void(void*, int)> callback);

  virtual int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data, void *arg,
      std::function<void(void*, int)> callback);

 private:
  int CreateLinkObject(const std::string& name,
      const std::string& hoid);
  int InitHeadObject(const std::string& hoid);

  static void aio_safe_cb_append(librados::completion_t cb, void *arg);
  static void aio_safe_cb_read(librados::completion_t cb, void *arg);

  static inline int zlog_rv(int ret);

  librados::IoCtx *ioctx_;
  std::string pool_;
};

#endif
