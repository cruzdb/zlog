// TODO:
//  - bufferlist encoding
#include <cerrno>
#include <sstream>
#include <boost/optional.hpp>
#include <rados/buffer.h>
#include <rados/objclass.h>
#include "roaring.c"
#include "roaring.hh"
#include "storage/ceph/cls_zlog.pb.h"
#include "storage/ceph/protobuf_bufferlist_adapter.h"

CLS_VER(1,0)
CLS_NAME(zlog)

#define HEAD_HEADER_KEY "zlog.head.header"
#define HEAD_VIEW_PREFIX "zlog.head.view."

class LogObjectHeader {
 public:
  explicit LogObjectHeader(const char *op_name) :
    op_name_(op_name)
  {}

  int read(cls_method_context_t hctx) {
    ceph::bufferlist bl;
    int ret = cls_cxx_getxattr(hctx, key, &bl);
    if (ret < 0) {
      // ENOENT is OK, but ENODATA means the object exists without a header. This
      // would be a violation of our basic protocol assumptions. Return an error
      // value that we won't catch.
      if (ret == -ENODATA) {
        CLS_ERR("ERROR: read_header(): object exists without header");
        return -EIO;
      }
      return ret;
    }

    if (!decode(bl, &hdr_)) {
      CLS_ERR("ERROR: read_header(): failed to decode header");
      return -EIO;
    }

    written_ = Roaring::read(hdr_.written().c_str(), false);
    invalid_ = Roaring::read(hdr_.invalid().c_str(), false);

    return 0;
  }

  int write(cls_method_context_t hctx) {
    size_t w_size = written_.getSizeInBytes();
    size_t i_size = invalid_.getSizeInBytes();
    char buf[std::max(w_size, i_size)];

    written_.write(buf, false);
    hdr_.set_written(buf, w_size);

    invalid_.write(buf, false);
    hdr_.set_invalid(buf, i_size);

    ceph::bufferlist bl;
    encode(bl, hdr_);
    return cls_cxx_setxattr(hctx, key, &bl);
  }

  int epoch_guard(uint64_t epoch, bool require_exists) {
    bool stale;
    if (hdr_.has_epoch()) {
      if (epoch < hdr_.epoch()) {
        stale = true;
      } else {
        stale = false;
      }
    } else if (require_exists) {
      stale = true;
    } else {
      stale = false;
    }
    if (stale) {
      CLS_LOG(10, "%s(): stale epoch", op_name_);
      return -ESPIPE;
    }
    return 0;
  }

  int check_or_init(uint32_t stride, uint32_t max_size,
      size_t entry_size)
  {
    if (hdr_.has_stride() || hdr_.has_max_size()) {
      if (!hdr_.has_stride() || !hdr_.has_max_size()) {
        CLS_ERR("ERROR: %s(): unexpected header state", op_name_);
        return -EIO;
      }
      if (hdr_.stride() != stride || hdr_.max_size() != max_size) {
        CLS_ERR("ERROR: %s(): op specs do not match header", op_name_);
        return -EINVAL;
      }
    } else {
      hdr_.set_stride(stride);
      hdr_.set_max_size(max_size);
    }

    if (entry_size > hdr_.max_size()) {
      CLS_ERR("ERROR: %s(): payload exceeds max size", op_name_);
      return -EINVAL;
    }

    return 0;
  }

  boost::optional<uint64_t> epoch() {
    if (hdr_.has_epoch()) {
      return hdr_.epoch();
    }
    return boost::none;
  }

  void set_epoch(uint64_t epoch) {
    hdr_.set_epoch(epoch);
  }

  boost::optional<uint64_t> max_pos() {
    if (hdr_.has_max_pos()) {
      return hdr_.max_pos();
    }
    return boost::none;
  }

  void set_max_pos(uint64_t pos) {
    if (!hdr_.has_max_pos() || (pos > hdr_.max_pos())) {
      hdr_.set_max_pos(pos);
    }
  }

  bool written(uint32_t bit) {
    return written_.contains(bit);
  }

  void set_written(uint32_t bit) {
    written_.add(bit);
  }

  bool invalid(uint32_t bit) {
    return invalid_.contains(bit);
  }

  void set_invalid(uint32_t bit) {
    invalid_.add(bit);
  }

 private:
  static constexpr const char *key = "zlog.data.header";
  const char *op_name_;
  zlog_ceph_proto::LogObjectHeader hdr_;
  Roaring written_;
  Roaring invalid_;
};

static inline std::string view_key(uint64_t epoch)
{
  std::stringstream ss;
  ss << HEAD_VIEW_PREFIX << std::setw(20) << std::setfill('0') << epoch;
  return ss.str();
}
 
static int view_read_header(cls_method_context_t hctx,
    zlog_ceph_proto::HeadObjectHeader& hdr)
{
  ceph::bufferlist bl;
  int ret = cls_cxx_getxattr(hctx, HEAD_HEADER_KEY, &bl);
  if (ret < 0) {
    if (ret == -ENODATA) {
      CLS_ERR("ERROR: view_read_header(): empty header");
      ret = -EIO;
    }
    return ret;
  }

  if (!decode(bl, &hdr)) {
    CLS_ERR("ERROR: view_read_header(): failed to decode meta");
    return -EIO;
  }

  return 0;
}

static int view_write_header(cls_method_context_t hctx,
    const zlog_ceph_proto::HeadObjectHeader& hdr)
{
  ceph::bufferlist bl;
  encode(bl, hdr);
  return cls_cxx_setxattr(hctx, HEAD_HEADER_KEY, &bl);
}

static int view_write_view(cls_method_context_t hctx, uint64_t epoch,
    const std::string& data)
{
  ceph::bufferlist bl;
  bl.append(data.c_str(), data.size());
  auto key = view_key(epoch);
  return cls_cxx_map_set_val(hctx, key, &bl);
}

static int view_read_view(cls_method_context_t hctx, uint64_t epoch,
    ceph::bufferlist& bl)
{
  auto key = view_key(epoch);
  return cls_cxx_map_get_val(hctx, key, &bl);
}

static int entry_read(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  zlog_ceph_proto::ReadEntry op;
  if (!decode(*in, &op)) {
    CLS_ERR("ERROR: read(): failed to decode input");
    return -EINVAL;
  }

  LogObjectHeader header("entry_read");
  int ret = header.read(hctx);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: read(): failed to read header");
    return ret;
  }

  ret = header.epoch_guard(op.epoch(), false);
  if (ret)
    return ret;

  ret = header.check_or_init(op.stride(), op.max_size(), 0);
  if (ret) {
    return ret;
  }

  const uint32_t index = op.pos() / op.stride();
  if (!header.written(index)) {
    CLS_LOG(10, "read(): entry not written");
    return -ENOENT;
  }

  if (header.invalid(index)) {
    CLS_LOG(10, "read(): entry is invalid");
    return -ENODATA;
  }

  const uint32_t slot_size = op.max_size();
  const uint32_t offset = index * slot_size;

  ret = cls_cxx_read(hctx, offset, slot_size, out);
  if (ret < 0) {
    CLS_ERR("ERROR: read(): failed to read slot %d", ret);
  }

  return 0;
}

static int entry_write(cls_method_context_t hctx, ceph::bufferlist *in, ceph::bufferlist *out)
{
  zlog_ceph_proto::WriteEntry op;
  if (!decode(*in, &op)) {
    CLS_ERR("ERROR: write(): failed to decode input");
    return -EINVAL;
  }

  LogObjectHeader header("entry_write");
  int ret = header.read(hctx);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: write(): failed to read header");
    return ret;
  }

  ret = header.epoch_guard(op.epoch(), false);
  if (ret)
    return ret;

  ret = header.check_or_init(op.stride(), op.max_size(),
      op.data().size());
  if (ret) {
    return ret;
  }

  const uint32_t index = op.pos() / op.stride();
  if (header.written(index)) {
    CLS_LOG(10, "write(): entry position non-empty");
    return -EROFS;
  }

  header.set_written(index);
  header.set_max_pos(op.pos());

  const uint32_t slot_size = op.max_size();
  const uint32_t offset = index * slot_size;

  ceph::bufferlist data;
  data.append(op.data());
  ret = cls_cxx_write(hctx, offset, data.length(), &data);
  if (ret < 0) {
    CLS_ERR("ERROR: write(): failed to write entry: %d", ret);
    return ret;
  }

  ret = header.write(hctx);
  if (ret < 0) {
    CLS_ERR("ERROR: write(): failed to write header %d", ret);
    return ret;
  }

  return 0;
}

static int entry_invalidate(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  zlog_ceph_proto::InvalidateEntry op;
  if (!decode(*in, &op)) {
    CLS_ERR("ERROR: invalidate(): failed to decode input");
    return -EINVAL;
  }

  LogObjectHeader header("entry_invalidate");
  int ret = header.read(hctx);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: invalidate(): failed to read header");
    return ret;
  }

  ret = header.epoch_guard(op.epoch(), false);
  if (ret)
    return ret;

  ret = header.check_or_init(op.stride(), op.max_size(), 0);
  if (ret) {
    return ret;
  }

  const uint32_t index = op.pos() / op.stride();
  if (header.written(index)) {
    if (header.invalid(index)) {
      CLS_LOG(10, "invalidate(): entry already invalidated");
      return 0;
    }
    if (!op.force()) {
      CLS_LOG(10, "invalidate(): entry position non-empty");
      return -EROFS;
    }
  }

  header.set_written(index);
  header.set_invalid(index);
  header.set_max_pos(op.pos());

  ret = header.write(hctx);
  if (ret < 0) {
    CLS_ERR("ERROR: invalidate(): failed to write header %d", ret);
    return ret;
  }

  return 0;
}

static int entry_seal(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  zlog_ceph_proto::Seal op;
  if (!decode(*in, &op)) {
    CLS_ERR("ERROR: seal(): failed to decode input");
    return -EINVAL;
  }

  LogObjectHeader header("entry_seal");
  int ret = header.read(hctx);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: seal(): read header failed: %d", ret);
    return ret;
  }

  auto epoch = header.epoch();
  if (epoch) {
    if (op.epoch() <= *epoch) {
      CLS_LOG(10, "entry_seal(): stale op epoch %llu <= %llu (hdr)",
          (unsigned long long)op.epoch(),
          (unsigned long long)*epoch);
      return -ESPIPE;
    }
  }

  header.set_epoch(op.epoch());

  ret = header.write(hctx);
  if (ret < 0) {
    CLS_ERR("ERROR: seal(): write header failed: %d", ret);
  }

  return 0;
}

static int entry_max_position(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  zlog_ceph_proto::ReadMaxPos op;
  if (!decode(*in, &op)) {
    CLS_ERR("ERROR: max_position(): failed to decode input");
    return -EINVAL;
  }

  LogObjectHeader header("entry_max_position");
  int ret = header.read(hctx);
  if (ret) {
    CLS_ERR("ERROR: max_position(): failed to read header: %d", ret);
    return ret;
  }

  auto epoch = header.epoch();
  if (epoch) {
    if (op.epoch() != *epoch) {
      CLS_LOG(10, "max_position(): op epoch %llu != %llu (hdr)",
          (unsigned long long)op.epoch(),
          (unsigned long long)*epoch);
      return -ESPIPE;
    }
  } else {
    CLS_ERR("ERROR: max_position(): expecting sealed object");
    return -EIO;
  }

  zlog_ceph_proto::MaxPos reply;
  auto max_pos = header.max_pos();
  if (max_pos) {
    reply.set_pos(*max_pos);
  }

  encode(*out, reply);

  return 0;
}

static int view_create(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  zlog_ceph_proto::CreateView op;
  if (!decode(*in, &op)) {
    CLS_ERR("ERROR: view_create(): failed to decode input");
    return -EINVAL;
  }

  zlog_ceph_proto::HeadObjectHeader head;
  int ret = view_read_header(hctx, head);
  if (ret < 0) {
    CLS_ERR("ERROR: view_create(): failed to read meta: %d", ret);
    return ret;
  }

  if (!head.has_max_epoch()) {
    if (op.epoch() != 0) {
      CLS_ERR("ERROR: view_create(): init with non-zero epoch");
      return -EINVAL;
    }
  } else if ((head.max_epoch() + 1) != op.epoch()) {
    CLS_ERR("ERROR: view_create(): bad epoch");
    return -EINVAL;
  }

  ret = view_write_view(hctx, op.epoch(), op.data());
  if (ret) {
    CLS_ERR("ERROR: view_create(): failed to write epoch view");
    return ret;
  }

  head.set_max_epoch(op.epoch());
  ret = view_write_header(hctx, head);
  if (ret) {
    CLS_ERR("ERROR: view_create(): failed to write meta");
    return ret;
  }

  return 0;
}

static int view_read(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  zlog_ceph_proto::ReadView op;
  if (!decode(*in, &op)) {
    CLS_ERR("ERROR: view_read(): failed to decode input");
    return -EINVAL;
  }

  zlog_ceph_proto::HeadObjectHeader head;
  int ret = view_read_header(hctx, head);
  if (ret < 0) {
    CLS_ERR("ERROR: view_read(): failed to read meta: %d", ret);
    return ret;
  }

  if (!head.has_max_epoch()) {
    CLS_ERR("ERROR: view_read(): head object not initialized");
    return -ENOENT;
  }

  uint32_t count = 0;
  uint64_t epoch = op.epoch();

  zlog_ceph_proto::Views views;

  while (epoch <= head.max_epoch() && count < op.max_views()) {
    ceph::bufferlist bl;
    ret = view_read_view(hctx, epoch, bl);
    if (ret < 0) {
      CLS_ERR("ERROR: view_read(): failed to read view: %d", ret);
      return ret;
    }

    auto view = views.add_views();
    view->set_epoch(epoch);
    view->set_data(bl.c_str(), bl.length());

    epoch++;
    count++;
  }

  encode(*out, views);

  return 0;
}

void __cls_init()
{
  CLS_LOG(0, "loading cls_zlog");

  // log data object methods
  cls_method_handle_t h_entry_read;
  cls_method_handle_t h_entry_write;
  cls_method_handle_t h_entry_invalidate;
  cls_method_handle_t h_entry_seal;
  cls_method_handle_t h_entry_max_position;

  // head object methods
  cls_method_handle_t h_view_create;
  cls_method_handle_t h_view_read;

  cls_handle_t h_class;
  cls_register("zlog", &h_class);

  cls_register_cxx_method(h_class, "entry_read",
      CLS_METHOD_RD,
      entry_read, &h_entry_read);

  cls_register_cxx_method(h_class, "entry_write",
      CLS_METHOD_RD | CLS_METHOD_WR,
      entry_write, &h_entry_write);

  cls_register_cxx_method(h_class, "entry_invalidate",
      CLS_METHOD_RD | CLS_METHOD_WR,
      entry_invalidate, &h_entry_invalidate);

  cls_register_cxx_method(h_class, "entry_seal",
      CLS_METHOD_RD | CLS_METHOD_WR,
      entry_seal, &h_entry_seal);

  cls_register_cxx_method(h_class, "entry_max_position",
      CLS_METHOD_RD,
      entry_max_position, &h_entry_max_position);

  cls_register_cxx_method(h_class, "view_create",
      CLS_METHOD_RD | CLS_METHOD_WR,
      view_create, &h_view_create);

  cls_register_cxx_method(h_class, "view_read",
      CLS_METHOD_RD,
      view_read, &h_view_read);
}
