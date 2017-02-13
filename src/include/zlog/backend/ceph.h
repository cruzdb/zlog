#ifndef ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>
#include "zlog/backend.h"
#include <iostream>
#include "proto/protobuf_bufferlist_adapter.h"

// v1
class CephBackend : public Backend {
 public:
  explicit CephBackend(librados::IoCtx *ioctx);

  virtual std::string pool();

  virtual int Exists(const std::string& oid);

  /*
   * Create the log metadata/head object and create the first projection. The
   * initial projection number is epoch = 0. Note that we don't initially seal
   * the objects that the log will be striped across. The semantics of
   * cls_zlog are such that unitialized objects behave exactly as if they had
   * been sealed with epoch = -1.
   *
   * The projection will be initialized for this log object during
   * RefreshProjection in the same way that it is done during Open().
   */
  virtual int CreateHeadObject(const std::string& oid,
      const zlog_proto::MetaLog& data);

  virtual int SetProjection(const std::string& oid, uint64_t epoch,
      const zlog_proto::MetaLog& data);

  /*
   *
   */
  virtual int LatestProjection(const std::string& oid,
      uint64_t *epoch, zlog_proto::MetaLog& config);

  virtual int Seal(const std::string& oid, uint64_t epoch);

  virtual int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos);

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

  virtual int AioAppend(const std::string& oid, uint64_t epoch,
      uint64_t position, const Slice& data, void *arg,
      std::function<void(void*, int)> callback);

  virtual int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data, void *arg,
      std::function<void(void*, int)> callback);

 private:
  static void aio_safe_cb_append(librados::completion_t cb, void *arg);
  static void aio_safe_cb_read(librados::completion_t cb, void *arg);

  static inline int zlog_rv(int ret);

  librados::IoCtx *ioctx_;
  std::string pool_;
};

#endif
