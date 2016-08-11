#ifndef ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>
#include "zlog/backend.h"
#include "libzlog/backend.h"

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
    return ioctx_->operate(oid, &op);
  }

  virtual int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position) {
    // prepare operation
    ceph::bufferlist data_bl;
    data_bl.append(data.data(), data.size());
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, epoch, position, data_bl);

    // run operation
    return ioctx_->operate(oid, &op);
  }

  virtual int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data) {
    // prepare operation
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, epoch, position);

    // run operation
    ceph::bufferlist bl;
    int ret = ioctx_->operate(oid, &op, &bl);

    if (ret == zlog::TmpBackend::CLS_ZLOG_OK) {
      data->assign(bl.c_str(), bl.length());
    }

    return ret;
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
    return ioctx_->operate(oid, &op);
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
    return ioctx_->operate(oid, &op);
  }

 private:
  librados::IoCtx *ioctx_;
};

#endif
