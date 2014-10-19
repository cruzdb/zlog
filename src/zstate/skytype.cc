#include <glog/logging.h>
#include <rados/buffer.h>
#include "../contrail/contrail.h"
#include "skytype.h"

using namespace skytype;

int SkyObject::update_helper(const void *data, size_t size)
{
  ceph::bufferptr bp((char*)data, size);
  ceph::bufferlist bl;
  bl.push_back(bp);

  int ret = log_.Append(bl);
  if (ret)
    return ret;

  return 0;
}

int SkyObject::query_helper()
{
  uint64_t tail;
  int ret = log_.CheckTail(&tail);
  if (ret)
    return ret;

  VLOG(1) << "query_helper: curpos " << position_ << " tail " << tail;

  while (position_ <= tail) {
    ceph::bufferlist bl;
    ret = log_.Read(position_, bl);
    switch (ret) {
      case 0:
        apply(bl.c_str());
        break;
      case contrail::Log::NOT_WRITTEN:
        ret = log_.Fill(position_);
        if (ret == contrail::Log::READ_ONLY)
          continue; // try again
        else if (ret)
          return ret;
        break;
      case contrail::Log::INVALIDATED:
        break;
      default:
        LOG(FATAL) << "unexpected return value ret " << ret;
        assert(0);
    }
    position_++;
  }

  return 0;
}
