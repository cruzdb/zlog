// TODO: add sanity check on sizes
// TODO: use bufferlist iterator
// TODO: max_size entry vs max_size WITH header
#include <cerrno>
#include <sstream>
#include <boost/lexical_cast.hpp>
#ifdef __CEPH__
# include "include/rados/buffer.h"
# include "include/rados/objclass.h"
# include "cls_zlog.pb.h"
# include "protobuf_bufferlist_adapter.h"
#else
# include <rados/buffer.h>
# include <rados/objclass.h>
# include "storage/ceph/cls_zlog.pb.h"
# include "storage/ceph/protobuf_bufferlist_adapter.h"
#endif

CLS_VER(1,0)
CLS_NAME(zlog)

// namespace for head object (sync with backend)
#define HEAD_HEADER_KEY "zlog.head.header"
#define HEAD_VIEW_PREFIX "zlog.head.view."

// namespace for log data objects
#define LOG_HEADER_KEY  "zlog.data.header"

// header prepended to each log entry. the exists flag is used to encode that an
// entry exists because when we read a hole rados will fill with zeros, and we
// need something to distinguish states.
class entry_header {
 public:
  entry_header() :
    flags_(0),
    size_(0),
    position_(0)
  {}

  bool exists() const {
    return (flags_ & 0x01) != 0;
  }

  bool invalid() const {
    return flags_ & 0x02;
  }

  void set_invalid(bool invalid) {
    if (invalid)
      flags_ |= 0x02;
    else
      flags_ &= 0xFD;
  }

  uint64_t position() const {
    return position_;
  }

  void set_position(uint64_t pos) {
    position_ = pos;
  }

  uint32_t size() const {
    return size_;
  }

  void set_size(uint32_t size) {
    size_ = size;
  }

  bool decode(ceph::bufferlist& bl) {
    if (bl.length() < sizeof(entry_header)) {
      return false;
    }
    const char *data = bl.c_str();
    flags_ = *((uint8_t*)data);
    data += sizeof(flags_);
    size_ = le32toh(*((uint32_t*)data));
    data += sizeof(size_);
    position_ = le64toh(*((uint64_t*)data));
    return true;
  }

  // this sets the exists flag in the output
  void encode(ceph::bufferlist& bl) {
    struct entry_header hdr;
    hdr.flags_ = flags_ | 0x01;
    hdr.size_ = htole32(size_);
    hdr.position_ = htole64(position_);
    bl.append((const char*)&hdr, sizeof(hdr));
  }

 private:
  uint8_t flags_;
  uint32_t size_;
  uint64_t position_;

} __attribute__((packed));

static inline std::string view_key(uint64_t epoch)
{
  std::stringstream ss;
  ss << HEAD_VIEW_PREFIX << std::setw(20) << std::setfill('0') << epoch;
  return ss.str();
}
 
static bool epoch_guard(const zlog_ceph_proto::LogObjectHeader& header,
    uint64_t epoch, bool require_exists)
{
  if (header.has_epoch()) {
    if (epoch < header.epoch())
      return true;
    return false;
  } else if (require_exists) {
    return true;
  } else {
    return false;
  }
}

static int get_object_size(cls_method_context_t hctx, uint64_t *size)
{
  int ret = cls_cxx_stat(hctx, size, NULL);
  if (ret < 0) {
    if (ret == -ENOENT) {
      *size = 0;
    } else {
      return ret;
    }
  }
  return 0;
}

static int entry_read_header(cls_method_context_t hctx,
    zlog_ceph_proto::LogObjectHeader& hdr)
{
  ceph::bufferlist bl;
  int ret = cls_cxx_getxattr(hctx, LOG_HEADER_KEY, &bl);
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

  if (!decode(bl, &hdr)) {
    CLS_ERR("ERROR: read_header(): failed to decode header");
    return -EIO;
  }

  return 0;
}

static int entry_write_header(cls_method_context_t hctx,
    const zlog_ceph_proto::LogObjectHeader& hdr)
{
  ceph::bufferlist bl;
  encode(bl, hdr);
  return cls_cxx_setxattr(hctx, LOG_HEADER_KEY, &bl);
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

  zlog_ceph_proto::LogObjectHeader header;
  int ret = entry_read_header(hctx, header);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: read(): failed to read header");
    return ret;
  }

  if (epoch_guard(header, op.epoch(), false)) {
    CLS_LOG(10, "read(): stale epoch");
    return -ESPIPE;
  }

  if (header.has_stride() || header.has_max_size()) {
    if (!header.has_stride() || !header.has_max_size()) {
      CLS_ERR("ERROR: read(): unexpected header state");
      return -EIO;
    }
    if (header.stride() != op.stride() ||
        header.max_size() != op.max_size()) {
      CLS_ERR("ERROR: read(): op specs do not match header");
      return -EINVAL;
    }
  }

  const uint32_t index = op.pos() / op.stride();
  const uint32_t slot_size = sizeof(entry_header) + op.max_size();
  const uint32_t offset = index * slot_size;

  uint64_t object_size;
  ret = get_object_size(hctx, &object_size);
  if (ret < 0) {
    CLS_ERR("ERROR: read(): get object size failed %d", ret);
    return ret;
  }

  if (offset < object_size) {
    ceph::bufferlist bl;
    ret = cls_cxx_read(hctx, offset, slot_size, &bl);
    if (ret < 0) {
      CLS_ERR("ERROR: read(): failed to read slot %d", ret);
      return ret;
    }

    entry_header hdr;
    if (!hdr.decode(bl)) {
      CLS_ERR("ERROR: read(): read incomplete header");
      return -EIO;
    }

    if (!hdr.exists()) {
      CLS_LOG(10, "read(): entry not written");
      return -ENOENT;
    }

    if (hdr.invalid()) {
      return -ENODATA;
    }

    out->append(bl.c_str() + sizeof(entry_header), hdr.size());

    return 0;
  }

  CLS_LOG(10, "read(): entry not written");
  return -ENOENT;
}

static int entry_write(cls_method_context_t hctx, ceph::bufferlist *in, ceph::bufferlist *out)
{
  zlog_ceph_proto::WriteEntry op;
  if (!decode(*in, &op)) {
    CLS_ERR("ERROR: write(): failed to decode input");
    return -EINVAL;
  }

  zlog_ceph_proto::LogObjectHeader header;
  int ret = entry_read_header(hctx, header);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: write(): failed to read header");
    return ret;
  }

  if (epoch_guard(header, op.epoch(), false)) {
    CLS_LOG(10, "write(): stale epoch");
    return -ESPIPE;
  }

  if (header.has_stride() || header.has_max_size()) {
    if (!header.has_stride() || !header.has_max_size()) {
      CLS_ERR("ERROR: write(): unexpected header state");
      return -EIO;
    }
    if (header.stride() != op.stride() ||
        header.max_size() != op.max_size()) {
      CLS_ERR("ERROR: write(): op specs do not match header");
      return -EINVAL;
    }
  } else {
    header.set_stride(op.stride());
    header.set_max_size(op.max_size());
    ret = entry_write_header(hctx, header);
    if (ret < 0) {
      CLS_ERR("ERROR: write(): failed to write header %d", ret);
      return ret;
    }
  }

  if (op.data().size() > header.max_size()) {
    CLS_ERR("ERROR: write(): payload exceeds max size");
    return -EINVAL;
  }

  const uint32_t index = op.pos() / header.stride();
  const uint32_t slot_size = sizeof(entry_header) + header.max_size();
  const uint32_t offset = index * slot_size;

  uint64_t object_size;
  ret = get_object_size(hctx, &object_size);
  if (ret < 0) {
    CLS_ERR("ERROR: write(): get object size failed: %d", ret);
    return ret;
  }

  if (offset < object_size) {
    ceph::bufferlist bl;
    ret = cls_cxx_read(hctx, offset, sizeof(entry_header), &bl);
    if (ret < 0) {
      CLS_ERR("ERROR: write(): failed to read entry header %d", ret);
      return ret;
    }

    entry_header hdr;
    if (!hdr.decode(bl)) {
      CLS_ERR("ERROR: write(): read incomplete entry header");
      return -EIO;
    }

    if (hdr.exists()) {
      CLS_LOG(10, "write(): entry position non-empty");
      return -EROFS;
    }
  }

  // write the new entry. when object_size <= offset we fall through to here
  // and update the object as a blind write since the target offset falls past
  // the end of the object.

  entry_header hdr;
  hdr.set_invalid(false);
  hdr.set_position(op.pos());
  hdr.set_size(op.data().size());

  ceph::bufferlist data;
  hdr.encode(data);
  data.append(op.data());

  ret = cls_cxx_write(hctx, offset, data.length(), &data);
  if (ret < 0) {
    CLS_ERR("ERROR: write(): failed to write entry: %d", ret);
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

  zlog_ceph_proto::LogObjectHeader header;
  int ret = entry_read_header(hctx, header);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: invalidate(): failed to read header");
    return ret;
  }

  if (epoch_guard(header, op.epoch(), false)) {
    CLS_LOG(10, "invalidate(): stale epoch");
    return -ESPIPE;
  }

  if (header.has_stride() || header.has_max_size()) {
    if (!header.has_stride() || !header.has_max_size()) {
      CLS_ERR("ERROR: invalidate(): unexpected header state");
      return -EIO;
    }
    if (header.stride() != op.stride() ||
        header.max_size() != op.max_size()) {
      CLS_ERR("ERROR: invalidate(): op specs do not match header");
      return -EINVAL;
    }
  } else {
    header.set_stride(op.stride());
    header.set_max_size(op.max_size());
    ret = entry_write_header(hctx, header);
    if (ret < 0) {
      CLS_ERR("ERROR: invalidate(): failed to write header %d", ret);
      return ret;
    }
  }

  const uint32_t index = op.pos() / header.stride();
  const uint32_t slot_size = sizeof(entry_header) + header.max_size();
  const uint32_t offset = index * slot_size;

  uint64_t object_size;
  ret = get_object_size(hctx, &object_size);
  if (ret < 0) {
    CLS_ERR("ERROR: invalidate(): get object size failed: %d", ret);
    return ret;
  }

  entry_header hdr;
  if (offset < object_size) {
    ceph::bufferlist bl;
    ret = cls_cxx_read(hctx, offset, sizeof(entry_header), &bl);
    if (ret < 0) {
      CLS_ERR("ERROR: invalidate(): failed to read entry header %d", ret);
      return ret;
    }

    if (!hdr.decode(bl)) {
      CLS_ERR("ERROR: invalidate(): read incomplete entry header");
      return -EIO;
    }

    if (hdr.exists()) {
      if (hdr.invalid()) {
        // already invalid
        return 0;
      }
      if (!op.force()) {
        CLS_LOG(10, "invalidate(): entry position non-empty");
        return -EROFS;
      }
    }

    // falling through maintains entry size
  }

  hdr.set_invalid(true);
  hdr.set_position(op.pos());

  ceph::bufferlist data;
  hdr.encode(data);

  cls_cxx_write(hctx, offset, data.length(), &data);
  if (ret < 0) {
    CLS_ERR("ERROR: invalidate(): failed to write entry header: %d", ret);
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

  zlog_ceph_proto::LogObjectHeader header;
  int ret = entry_read_header(hctx, header);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: seal(): read header failed: %d", ret);
    return ret;
  }

  if (header.has_epoch()) {
    if (op.epoch() <= header.epoch()) {
      CLS_LOG(10, "seal(): stale op epoch %llu <= %llu (hdr)",
          (unsigned long long)op.epoch(),
          (unsigned long long)header.epoch());
      return -ESPIPE;
    }
  }

  header.set_epoch(op.epoch());

  ret = entry_write_header(hctx, header);
  if (ret < 0)
    CLS_ERR("ERROR: seal(): write header failed: %d", ret);

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

  zlog_ceph_proto::LogObjectHeader header;
  int ret = entry_read_header(hctx, header);
  if (ret) {
    CLS_ERR("ERROR: max_position(): failed to read header: %d", ret);
    return ret;
  }

  if (header.has_epoch()) {
    if (op.epoch() != header.epoch()) {
      CLS_LOG(10, "max_position(): op epoch %llu != %llu (hdr)",
          (unsigned long long)op.epoch(),
          (unsigned long long)header.epoch());
      return -ESPIPE;
    }
  } else {
    CLS_ERR("ERROR: max_position(): expecting sealed object");
    return -EIO;
  }

  uint64_t object_size;
  ret = get_object_size(hctx, &object_size);
  if (ret < 0) {
    CLS_ERR("ERROR: max_position(): get object size failed: %d", ret);
    return ret;
  }

  zlog_ceph_proto::MaxPos reply;
  if (object_size > 0) {
    if (!header.has_stride() || !header.has_max_size()) {
      CLS_ERR("ERROR: write(): unexpected header state");
      return -EIO;
    }

    const uint32_t slot_size = sizeof(entry_header) + header.max_size();
    uint64_t offset = (object_size - 1) - ((object_size - 1) % slot_size);

    ceph::bufferlist bl;
    ret = cls_cxx_read(hctx, offset, sizeof(entry_header), &bl);
    if (ret < 0) {
      CLS_ERR("ERROR: max_position(): failed to read entry header %d", ret);
      return ret;
    }

    entry_header hdr;
    if (!hdr.decode(bl)) {
      CLS_ERR("ERROR: max_position(): read incomplete entry header");
      return -EIO;
    }

    if (!hdr.exists()) {
      CLS_ERR("ERROR: max_position(): invalid object state");
      return -EIO;
    }

    reply.set_pos(hdr.position());
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
