// TODO
//  - add hostname to head object name
//  - share xattr key with cls_zlog
#include <sstream>
#include "zlog/backend/ceph.h"
#include "cls_zlog_client.h"
#include "storage/ceph/cls_zlog.pb.h"

// namespace for head object (sync with cls_zlog)
#define HEAD_HEADER_KEY "zlog.head.header"

CephBackend::CephBackend(librados::IoCtx *ioctx) :
  ioctx_(ioctx)
{
  pool_ = ioctx_->get_pool_name();
}

int CephBackend::CreateLog(const std::string& name,
    const std::string& initial_view)
{
  if (name.empty())
    return -EINVAL;

  struct timeval tv;
  int ret = gettimeofday(&tv, NULL);
  if (ret)
    return ret;

  // create the head object. ensure a unique name, and that it is initialized to
  // a state that could be used to later identify it as orphaned (e.g. age +
  // uninitialized state). it's important that the head object be uniquely
  // named, because if it is not unique then if we crash immediately after
  // creating a link to the head (see below), then two names may point to the
  // same log.
  std::string hoid;
  while (true) {
    std::stringstream head_ss;
    head_ss << "zlog.head." << name << "."
      << tv.tv_sec << "." << tv.tv_usec;
    hoid = head_ss.str();

    ret = ioctx_->create(hoid, true);
    if (ret) {
      if (ret == -EEXIST)
        continue;
      return ret;
    }

    break;
  }

  // the head object now exists, but is orphaned. a crash at this point is ok
  // because a gc process could later remove it. now we'll build a link from the
  // log name requested to the head object we just created.
  ret = CreateLinkObject(name, hoid);
  if (ret) {
    std::cerr << "create link obj ret " << ret << std::endl;
    return ret;
  }

  // now the named log exists and points to a head object. a crash at this point
  // is ok because a client could complete the initialization. TODO: crash
  // recovery here is not yet implemented. if a crash occurs, then a client will
  // encounter an error when opening the log.  the head object is initialized
  // with some metadata and a view for epoch 0. TODO: note the race that exists
  // between head initialization, and future feature that handles initialization
  // of the head object for the crash-during-creation case.
  ret = InitHeadObject(hoid);
  if (ret) {
    std::cerr << "init head obj ret " << ret << std::endl;
    return ret;
  }

  // initialize the head object by setting its epoch 0 view
  ret = ProposeView(hoid, 0, initial_view);
  if (ret) {
    std::cerr << "propose view ret " << ret << std::endl;
    return ret;
  }

  return ret;
}

int CephBackend::OpenLog(const std::string& name,
    std::string& prefix)
{
  zlog_ceph_proto::LinkObjectHeader link;
  {
    ceph::bufferlist bl;
    auto loid = LinkObjectName(name);
    int ret = ioctx_->read(loid, bl, 0, 0);
    if (ret < 0) {
      return ret;
    }

    if (!unpack_msg<zlog_ceph_proto::LinkObjectHeader>(link, bl))
      return -EIO;
  }

  auto hoid = link.hoid();

  zlog_ceph_proto::HeadObjectHeader head;
  {
    ceph::bufferlist bl;
    int ret = ioctx_->getxattr(hoid, HEAD_HEADER_KEY, bl);
    if (ret < 0) {
      return ret;
    }
    if (!unpack_msg<zlog_ceph_proto::HeadObjectHeader>(head, bl))
      return -EIO;
  }

  if (head.deleted())
    return -ENOENT;

  prefix = hoid;

  return 0;
}

int CephBackend::ReadViews(const std::string& hoid,
    uint64_t epoch, std::map<uint64_t, std::string>& out)
{
  std::map<uint64_t, std::string> tmp;

  // read views starting with specified epoch
  librados::ObjectReadOperation op;
  zlog::cls_zlog_read_view(op, epoch);
  ceph::bufferlist bl;
  int ret = ioctx_->operate(hoid, &op, &bl);
  if (ret)
    return ret;

  zlog_ceph_proto::Views views;
  if (!unpack_msg<zlog_ceph_proto::Views>(views, bl))
    return -EIO;

  // unpack into return map
  for (int i = 0; i < views.views_size(); i++) {
    auto view = views.views(i);
    std::string data(view.data().c_str(), view.data().size());
    auto res = tmp.emplace(view.epoch(), data);
    assert(res.second);
  }

  out.swap(tmp);

  return 0;
}

int CephBackend::ProposeView(const std::string& hoid,
    uint64_t epoch, const std::string& view)
{
  ceph::bufferlist bl;
  bl.append(view.c_str(), view.size());
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_create_view(op, epoch, bl);
  int ret = ioctx_->operate(hoid, &op);
  return ret;
}

int CephBackend::Read(const std::string& oid, uint64_t epoch,
                      uint64_t position, std::string *data)
{
  librados::ObjectReadOperation op;
  zlog::cls_zlog_read(op, epoch, position);

  ceph::bufferlist bl;
  int ret = ioctx_->operate(oid, &op, &bl);
  if (ret)
    return ret;

  data->assign(bl.c_str(), bl.length());

  return 0;
}

int CephBackend::Write(const std::string& oid, const Slice& data,
          uint64_t epoch, uint64_t position)
{
  ceph::bufferlist data_bl;
  data_bl.append(data.data(), data.size());

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_write(op, epoch, position, data_bl);

  return ioctx_->operate(oid, &op);
}

int CephBackend::Fill(const std::string& oid, uint64_t epoch,
    uint64_t position)
{
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_fill(op, epoch, position);

  return ioctx_->operate(oid, &op);
}

int CephBackend::Trim(const std::string& oid, uint64_t epoch,
                      uint64_t position)
{
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_trim(op, epoch, position);

  return ioctx_->operate(oid, &op);
}

int CephBackend::Seal(const std::string& oid, uint64_t epoch)
{
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_seal(op, epoch);

  return ioctx_->operate(oid, &op);
}

int CephBackend::MaxPos(const std::string& oid, uint64_t epoch,
           uint64_t *pos, bool *empty)
{
  int rv;
  librados::ObjectReadOperation op;
  zlog::cls_zlog_max_position(op, epoch, pos, empty, &rv);

  int ret = ioctx_->operate(oid, &op, NULL);
  if (ret < 0)
    return ret;
  if (rv < 0)
    return rv;

  return 0;
}

int CephBackend::AioRead(const std::string& oid, uint64_t epoch,
    uint64_t position, std::string *data, void *arg,
    std::function<void(void*, int)> callback)
{
  AioContext *c = new AioContext;
  c->arg = arg;
  c->cb = callback;
  c->data = data;
  c->c = librados::Rados::aio_create_completion(c,
      NULL, CephBackend::aio_safe_cb_read);
  assert(c->c);

  librados::ObjectReadOperation op;
  zlog::cls_zlog_read(op, epoch, position);

  return ioctx_->aio_operate(oid, c->c, &op, &c->bl);
}

int CephBackend::AioWrite(const std::string& oid, uint64_t epoch,
    uint64_t position, const Slice& data, void *arg,
    std::function<void(void*, int)> callback)
{
  AioContext *c = new AioContext;
  c->arg = arg;
  c->cb = callback;
  c->data = NULL;
  c->c = librados::Rados::aio_create_completion(c,
      NULL, CephBackend::aio_safe_cb_append);
  assert(c->c);

  ceph::bufferlist data_bl;
  data_bl.append(data.data(), data.size());

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_write(op, epoch, position, data_bl);

  return ioctx_->aio_operate(oid, c->c, &op);
}

std::string CephBackend::LinkObjectName(const std::string& name)
{
  std::stringstream ss;
  ss << "zlog.link." << name;
  return ss.str();
}

int CephBackend::CreateLinkObject(const std::string& name,
    const std::string& hoid)
{
  zlog_ceph_proto::LinkObjectHeader meta;
  meta.set_hoid(hoid);

  ceph::bufferlist bl;
  pack_msg<zlog_ceph_proto::LinkObjectHeader>(bl, meta);

  librados::ObjectWriteOperation op;
  op.create(true);
  op.write_full(bl);

  auto loid = LinkObjectName(name);

  int ret = ioctx_->operate(loid, &op);
  return ret;
}

int CephBackend::InitHeadObject(const std::string& hoid)
{
  zlog_ceph_proto::HeadObjectHeader meta;
  meta.set_deleted(false);
  // don't set max_epoch...
  assert(!meta.has_max_epoch());

  ceph::bufferlist bl;
  pack_msg<zlog_ceph_proto::HeadObjectHeader>(bl, meta);

  librados::ObjectWriteOperation op;
  op.assert_exists();
  op.setxattr(HEAD_HEADER_KEY, bl);

  int ret = ioctx_->operate(hoid, &op);
  return ret;
}

void CephBackend::aio_safe_cb_append(librados::completion_t cb, void *arg)
{
  AioContext *c = (AioContext*)arg;
  librados::AioCompletion *rc = c->c;
  int ret = rc->get_return_value();
  rc->release();
  c->cb(c->arg, ret);
  delete c;
}

void CephBackend::aio_safe_cb_read(librados::completion_t cb, void *arg)
{
  AioContext *c = (AioContext*)arg;
  librados::AioCompletion *rc = c->c;
  int ret = rc->get_return_value();
  rc->release();
  if (ret == zlog::CLS_ZLOG_OK && c->bl.length() > 0)
    c->data->assign(c->bl.c_str(), c->bl.length());
  c->cb(c->arg, ret);
  delete c;
}
