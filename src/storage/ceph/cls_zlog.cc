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
#define LOG_ENTRY_PREFIX "zlog.data.entry."
#define LOG_HEADER_KEY  "zlog.data.header"

static inline std::string u64tostr(uint64_t value,
    const std::string& prefix)
{
  std::stringstream ss;
  ss << prefix << std::setw(20) << std::setfill('0') << value;
  return ss.str();
}

static inline std::string entry_key(uint64_t pos)
{
  return u64tostr(pos, LOG_ENTRY_PREFIX);
}

static inline std::string view_key(uint64_t epoch)
{
  return u64tostr(epoch, HEAD_VIEW_PREFIX);
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

static int entry_read_entry(cls_method_context_t hctx, const std::string& key,
    zlog_ceph_proto::LogEntry *entry)
{
  ceph::bufferlist bl;
  int ret = cls_cxx_map_get_val(hctx, key, &bl);
  if (ret < 0)
    return ret;
  if (entry && !decode(bl, entry))
    return -EIO;
  return 0;
}

static int entry_write_entry(cls_method_context_t hctx, const std::string& key,
    const zlog_ceph_proto::LogEntry& entry)
{
  ceph::bufferlist bl;
  encode(bl, entry);
  return cls_cxx_map_set_val(hctx, key, &bl);
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

  zlog_ceph_proto::LogEntry entry;
  auto key = entry_key(op.pos());
  ret = entry_read_entry(hctx, key, &entry);
  if (ret < 0) {
    if (ret == -ENOENT)
      CLS_LOG(10, "read(): entry not written");
    else
      CLS_ERR("ERROR: read(): failed to read entry");
    return ret;
  }

  if (entry.flags() & zlog_ceph_proto::LogEntry::INVALID) {
    return -ENODATA;

  } else if (entry.flags() != 0) {
    CLS_ERR("ERROR: read(): unexpected state");
    return -EIO;
  }

  ret = cls_cxx_read(hctx, entry.offset(), entry.length(), out);
  if (ret < 0) {
    CLS_ERR("ERROR: read(): failed to read entry: %d", ret);
    return ret;
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

  auto key = entry_key(op.pos());
  ret = entry_read_entry(hctx, key, NULL);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: write(): failed to read entry");
    return ret;
  }

  if (ret == -ENOENT) {
    // get object size
    uint64_t obj_size;
    ret = cls_cxx_stat(hctx, &obj_size, NULL);
    if (ret < 0) {
      if (ret == -ENOENT) {
        obj_size = 0;
      } else {
        CLS_ERR("ERROR: write(): stat failed: %D", ret);
        return ret;
      }
    }

    ceph::bufferlist entry_bl;
    entry_bl.append(op.data());

    zlog_ceph_proto::LogEntry entry;
    entry.set_offset(obj_size);
    entry.set_length(entry_bl.length());

    ret = cls_cxx_write(hctx, obj_size, entry_bl.length(), &entry_bl);
    if (ret < 0) {
      CLS_ERR("ERROR: write(): failed to write entry: %d", ret);
      return ret;
    }

    ret = entry_write_entry(hctx, key, entry);
    if (ret < 0) {
      CLS_ERR("ERROR: write(): failed to write entry");
      return ret;
    }

    if (!header.has_max_pos() || (op.pos() > header.max_pos()))
      header.set_max_pos(op.pos());

    ret = entry_write_header(hctx, header);
    if (ret < 0) {
      CLS_ERR("ERROR: write(): failed to write header");
      return ret;
    }

    return 0;

  } else if (ret == 0) {
    CLS_LOG(10, "write(): entry position non-empty");
    return -EROFS;

  } else {
    CLS_ERR("ERROR: write(): unexpected return value %d", ret);
    return -EIO;
  }
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

  auto key = entry_key(op.pos());
  zlog_ceph_proto::LogEntry entry;
  ret = entry_read_entry(hctx, key, &entry);
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: invalidate(): failed to read entry");
    return ret;
  }

  if (ret == -ENOENT) {
    // invalidate entry. not forced
    entry.set_flags(zlog_ceph_proto::LogEntry::INVALID);
    ret = entry_write_entry(hctx, key, entry);
    if (ret < 0) {
      CLS_ERR("ERROR: invalidate(): failed to write entry");
      return ret;
    }

    if (!header.has_max_pos() || (op.pos() > header.max_pos()))
      header.set_max_pos(op.pos());

    ret = entry_write_header(hctx, header);
    if (ret < 0) {
      CLS_ERR("ERROR: invalidate(): failed to write header");
      return ret;
    }

    return 0;

  } else if (entry.flags() & zlog_ceph_proto::LogEntry::INVALID) {
    // already invalid. preserve data and forced flag
    return 0;

  } else if (entry.flags() != 0) {
    CLS_ERR("ERROR: invalidate(): unexpected state");
    return -EIO;

  } else if (!op.force()) {
    CLS_LOG(10, "invalidate(): entry position non-empty");
    return -EROFS;

  } else {
    // force invalidate entry. preserve data. no need to update the max position
    // in the header because this position would already be reflected in that
    // value.
    entry.set_flags(zlog_ceph_proto::LogEntry::INVALID |
        zlog_ceph_proto::LogEntry::FORCED);
    ret = entry_write_entry(hctx, key, entry);
    if (ret < 0)
      CLS_ERR("ERROR: invalidate(): failed to write entry");
    return ret;
  }
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

  zlog_ceph_proto::MaxPos reply;
  if (header.has_max_pos())
    reply.set_pos(header.max_pos());

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

  // view management
  cls_register_cxx_method(h_class, "view_create",
      CLS_METHOD_RD | CLS_METHOD_WR,
      view_create, &h_view_create);

  cls_register_cxx_method(h_class, "view_read",
      CLS_METHOD_RD,
      view_read, &h_view_read);
}
