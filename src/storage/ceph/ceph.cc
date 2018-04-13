#include <sstream>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include "storage/ceph/protobuf_bufferlist_adapter.h"
#include "zlog/backend/ceph.h"
#include "cls_zlog_client.h"
#include "storage/ceph/cls_zlog.pb.h"

namespace zlog {
namespace storage {
namespace ceph {

// TODO: make this constructor private and used by the plugin-based allocator
// interface. Same for the destructor.
CephBackend::CephBackend() :
  cluster_(nullptr),
  ioctx_(nullptr)
{
}

CephBackend::CephBackend(librados::IoCtx *ioctx) :
  cluster_(nullptr),
  ioctx_(ioctx),
  pool_(ioctx_->get_pool_name())
{
  // TODO: even when a backend is created explicitly, it needs to fill in enough
  // options so that a sequencer can open an instance. Or not. In our case def.
  options["scheme"] = "ceph";
  options["conf_file"] = "";
  options["pool"] = pool_;
}

CephBackend::~CephBackend()
{
  // cluster_ is only non-null when it was created via Initialize() in which
  // case the backend owns both the cluster and ioctx and needs to release them.
  if (cluster_) {
    ioctx_->close();
    delete ioctx_;
    cluster_->shutdown();
    delete cluster_;
  }
}

// TODO: even when a backend is created explicitly, it needs to fill in enough
// options so that a sequencer can open an instance. Or not. In our case def.
std::map<std::string, std::string> CephBackend::meta()
{
  return options;
}

int CephBackend::Initialize(
    const std::map<std::string, std::string>& opts)
{
  auto cluster = new librados::Rados;

  // initialize cluster
  auto it = opts.find("id");
  auto id = it == opts.end() ? nullptr : it->second.c_str();
  int ret = cluster->init(id);
  if (ret) {
    delete cluster;
    return ret;
  }

  // read conf file?
  it = opts.find("conf_file");
  if (it != opts.end()) {
    auto conf_file = it->second.empty() ? nullptr : it->second.c_str();
    ret = cluster->conf_read_file(conf_file);
    if (ret) {
      delete cluster;
      return ret;
    }
  }

  ret = cluster->connect();
  if (ret) {
    delete cluster;
    return ret;
  }

  // pool
  it = opts.find("pool");
  auto pool = it == opts.end() ? "zlog" : it->second;

  auto ioctx = new librados::IoCtx;
  ret = cluster->ioctx_create(pool.c_str(), *ioctx);
  if (ret) {
    delete ioctx;
    cluster->shutdown();
    delete cluster;
    return ret;
  }

  options = opts;
  options["scheme"] = "ceph";

  cluster_ = cluster;
  ioctx_ = ioctx;
  pool_ = ioctx_->get_pool_name();

  return 0;
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
  // a state that could be used to later identify it as orphaned (e.g. use rados
  // mtime and/or unitialized state). it's important that the head object be
  // uniquely named, because if it is not unique then if we crash immediately
  // after creating a link to the head (see below), then two names may point to
  // the same log.
  std::string hoid;
  std::string prefix;
  while (true) {
    boost::uuids::uuid uuid = boost::uuids::random_generator()();
    prefix = boost::uuids::to_string(uuid);

    std::stringstream hoid_ss;
    hoid_ss << "zlog.head." << prefix;
    hoid = hoid_ss.str();

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
  // is ok because a client could complete the initialization.
  ret = InitHeadObject(hoid, prefix);
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
    std::string& hoid, std::string& prefix)
{
  zlog_ceph_proto::LinkObjectHeader link;
  {
    ::ceph::bufferlist bl;
    auto loid = LinkObjectName(name);
    int ret = ioctx_->read(loid, bl, 0, 0);
    if (ret < 0) {
      return ret;
    }

    if (!decode(bl, &link))
      return -EIO;
  }

  hoid = link.hoid();

  zlog_ceph_proto::HeadObjectHeader head;
  {
    ::ceph::bufferlist bl;
    int ret = ioctx_->getxattr(hoid, HEAD_HEADER_KEY, bl);
    if (ret < 0) {
      return ret;
    }
    if (!decode(bl, &head))
      return -EIO;
  }

  if (head.deleted())
    return -ENOENT;

  prefix = head.prefix();
  if (prefix.empty())
    return -EIO;

  return 0;
}

int CephBackend::ReadViews(const std::string& hoid,
    uint64_t epoch, std::map<uint64_t, std::string>& out)
{
  std::map<uint64_t, std::string> tmp;

  // read views starting with specified epoch
  librados::ObjectReadOperation op;
  zlog::cls_zlog_read_view(op, epoch);
  ::ceph::bufferlist bl;
  int ret = ioctx_->operate(hoid, &op, &bl);
  if (ret)
    return ret;

  zlog_ceph_proto::Views views;
  if (!decode(bl, &views))
    return -EIO;

  // unpack into return map
  for (int i = 0; i < views.views_size(); i++) {
    auto view = views.views(i);
    std::string data(view.data().c_str(), view.data().size());
    auto res = tmp.emplace(view.epoch(), data);
    assert(res.second);
    (void)res;
  }

  out.swap(tmp);

  return 0;
}

int CephBackend::ProposeView(const std::string& hoid,
    uint64_t epoch, const std::string& view)
{
  ::ceph::bufferlist bl;
  bl.append(view.c_str(), view.size());
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_create_view(op, epoch, bl);
  int ret = ioctx_->operate(hoid, &op);
  return ret;
}

int CephBackend::Read(const std::string& oid, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size, std::string *data)
{
  librados::ObjectReadOperation op;
  zlog::cls_zlog_read(op, epoch, position, stride, max_size);

  ::ceph::bufferlist bl;
  int ret = ioctx_->operate(oid, &op, &bl);
  if (ret)
    return ret;

  data->assign(bl.c_str(), bl.length());

  return 0;
}

int CephBackend::Write(const std::string& oid, const Slice& data,
          uint64_t epoch, uint64_t position, uint32_t stride, uint32_t max_size)
{
  ::ceph::bufferlist data_bl;
  data_bl.append(data.data(), data.size());

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_write(op, epoch, position, stride, max_size, data_bl);

  return ioctx_->operate(oid, &op);
}

int CephBackend::Fill(const std::string& oid, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size)
{
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_invalidate(op, epoch, position, stride, max_size, false);

  return ioctx_->operate(oid, &op);
}

int CephBackend::Trim(const std::string& oid, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size)
{
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_invalidate(op, epoch, position, stride, max_size, true);

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
    uint64_t position, uint32_t stride, uint32_t max_size,
    std::string *data, void *arg,
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
  zlog::cls_zlog_read(op, epoch, position, stride, max_size);

  return ioctx_->aio_operate(oid, c->c, &op, &c->bl);
}

int CephBackend::AioWrite(const std::string& oid, uint64_t epoch,
    uint64_t position, uint32_t stride, uint32_t max_size,
    const Slice& data, void *arg,
    std::function<void(void*, int)> callback)
{
  AioContext *c = new AioContext;
  c->arg = arg;
  c->cb = callback;
  c->data = NULL;
  c->c = librados::Rados::aio_create_completion(c,
      NULL, CephBackend::aio_safe_cb_append);
  assert(c->c);

  ::ceph::bufferlist data_bl;
  data_bl.append(data.data(), data.size());

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_write(op, epoch, position, stride, max_size, data_bl);

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

  ::ceph::bufferlist bl;
  encode(bl, meta);

  librados::ObjectWriteOperation op;
  op.create(true);
  op.write_full(bl);

  auto loid = LinkObjectName(name);

  int ret = ioctx_->operate(loid, &op);
  return ret;
}

int CephBackend::InitHeadObject(const std::string& hoid,
    const std::string& prefix)
{
  librados::ObjectWriteOperation op;
  zlog::cls_zlog_init_head(op, prefix);
  return ioctx_->operate(hoid, &op);
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
  if (ret == 0 && c->bl.length() > 0)
    c->data->assign(c->bl.c_str(), c->bl.length());
  c->cb(c->arg, ret);
  delete c;
}

extern "C" Backend *__backend_allocate(void)
{
  auto b = new CephBackend();
  return b;
}

extern "C" void __backend_release(Backend *p)
{
  // TODO: whats the correct type of cast here
  CephBackend *backend = (CephBackend*)p;
  delete backend;
}

}
}
}
