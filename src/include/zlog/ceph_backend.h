#ifndef ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>
#include "zlog/backend.h"

// v1
class CephBackend : public Backend {
 public:
  explicit CephBackend(librados::IoCtx *ioctx) :
    Backend(ioctx), ioctx_(ioctx)
  {}

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
  int CreateHeadObject(const std::string& oid, ceph::bufferlist& bl) {
    // prepare operation
    librados::ObjectWriteOperation op;
    op.create(true); // exclusive create
    zlog::cls_zlog_set_projection(op, 0, bl);

    // run operation
    int ret = ioctx_->operate(oid, &op);
    return rv(ret);
  }

  virtual int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position) {
    // prepare operation
    ceph::bufferlist data_bl;
    data_bl.append(data.data(), data.size());
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, epoch, position, data_bl);

    // run operation
    int ret = ioctx_->operate(oid, &op);
    return rv(ret);
  }

  virtual int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data) {
    // prepare operation
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, epoch, position);

    // run operation
    ceph::bufferlist bl;
    int ret = ioctx_->operate(oid, &op, &bl);

    // success: copy data out
    if (ret == zlog::CLS_ZLOG_OK)
      data->assign(bl.c_str(), bl.length());

    return rv(ret);
  }

  /*
   *
   */
  virtual int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position) {
    // prepare operation
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_trim(op, epoch, position);

    // run operation
    int ret = ioctx_->operate(oid, &op);
    return rv(ret);
  }

  /*
   *
   */
  virtual int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position) {
    // prepare operation
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, epoch, position);

    // run operation
    int ret = ioctx_->operate(oid, &op);
    return rv(ret);
  }

 private:
  static inline int rv(int ret) {
    if (ret < 0)
      return ret;

    switch (ret) {
      case zlog::CLS_ZLOG_OK:
        return Backend::ZLOG_OK;

      case zlog::CLS_ZLOG_STALE_EPOCH:
        return Backend::ZLOG_STALE_EPOCH;

      case zlog::CLS_ZLOG_READ_ONLY:
        return Backend::ZLOG_READ_ONLY;

      case zlog::CLS_ZLOG_NOT_WRITTEN:
        return Backend::ZLOG_NOT_WRITTEN;

      case zlog::CLS_ZLOG_INVALIDATED:
        return Backend::ZLOG_INVALIDATED;

      case zlog::CLS_ZLOG_INVALID_EPOCH:
        return Backend::ZLOG_INVALID_EPOCH;

      default:
        assert(0);
        return -EIO;
    }
  }

  librados::IoCtx *ioctx_;
};

#endif
