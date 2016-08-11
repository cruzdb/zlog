#ifndef ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_CEPH_BACKEND_H
#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>
#include "zlog/backend.h"

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

 private:
  librados::IoCtx *ioctx_;
};

#endif
