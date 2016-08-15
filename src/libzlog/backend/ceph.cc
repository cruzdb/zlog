#include "zlog/backend/ceph.h"

CephBackend::CephBackend(librados::IoCtx *ioctx) :
  Backend(ioctx), ioctx_(ioctx)
{
  pool_ = ioctx_->get_pool_name();
}
