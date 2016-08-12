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
  explicit CephBackend(librados::IoCtx *ioctx) :
    Backend(ioctx), ioctx_(ioctx)
  {
    pool_ = ioctx_->get_pool_name();
  }

  virtual std::string pool() {
    return pool_;
  }

  virtual int Exists(const std::string& oid) {
    int ret = ioctx_->stat(oid, NULL, NULL);
    return zlog_rv(ret);
  }

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
      const zlog_proto::MetaLog& data) {
    // prepare blob
    ceph::bufferlist bl;
    pack_msg<zlog_proto::MetaLog>(bl, data);

    // prepare operation
    librados::ObjectWriteOperation op;
    op.create(true); // exclusive create
    zlog::cls_zlog_set_projection(op, 0, bl);

    // run operation
    int ret = ioctx_->operate(oid, &op);
    return zlog_rv(ret);
  }

  virtual int SetProjection(const std::string& oid, uint64_t epoch,
      const zlog_proto::MetaLog& data) {
    // prepare blob
    ceph::bufferlist bl;
    pack_msg<zlog_proto::MetaLog>(bl, data);

    // prepare operation
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_set_projection(op, epoch, bl);

    // run operation
    int ret = ioctx_->operate(oid, &op);
    return zlog_rv(ret);
  }

  /*
   *
   */
  virtual int LatestProjection(const std::string& oid,
      uint64_t *epoch, zlog_proto::MetaLog& config) {
    // prepare operation
    int rv;
    ceph::bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_get_latest_projection(op, &rv, epoch, &bl);

    // run operation
    ceph::bufferlist unused;
    int ret = ioctx_->operate(oid, &op, &unused);
    if (ret || rv) {
      std::cerr << "LatestProjection: rv " << rv
        << " ret " << ret << std::endl;
      if (ret)
        return zlog_rv(ret);
      if (rv)
        return zlog_rv(rv);
    }

    // copy out data
    if (!unpack_msg<zlog_proto::MetaLog>(config, bl)) {
      std::cerr << "failed to parse configuration" << std::endl;
      return -EIO;
    }

    return zlog_rv(0);
  }

  virtual int Seal(const std::string& oid, uint64_t epoch) {
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_seal(op, epoch);
    int ret = ioctx_->operate(oid, &op);
    return zlog_rv(ret);
  }

  virtual int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos) {
    // prepare operation
    int rv;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_max_position(op, epoch, pos, &rv);

    // run operation
    ceph::bufferlist unused;
    int ret = ioctx_->operate(oid, &op, &unused);
    if (ret || rv) {
      std::cerr << "MaxPos ret " << ret << " rv " << rv << std::endl;
      if (ret)
        return zlog_rv(ret);
      if (rv)
        return zlog_rv(rv);
    }

    return zlog_rv(0);
  }

  /*
   *
   */
  virtual int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position) {
    // prepare operation
    ceph::bufferlist data_bl;
    data_bl.append(data.data(), data.size());
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, epoch, position, data_bl);

    // run operation
    int ret = ioctx_->operate(oid, &op);
    return zlog_rv(ret);
  }

  /*
   *
   */
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

    return zlog_rv(ret);
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
    return zlog_rv(ret);
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
    return zlog_rv(ret);
  }

 private:
  static inline int zlog_rv(int ret) {
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
  std::string pool_;
};

#endif
