#pragma once
#include <cerrno>
#include <sstream>
#include <string>
#include <boost/optional.hpp>
#include <rados/buffer.h>
#include <rados/objclass.h>
#include "storage/ceph/cls_zlog.pb.h"
#include "storage/ceph/protobuf_bufferlist_adapter.h"

#define ZLOG_MAX_VIEW_READS ((uint32_t)100)
#define ZLOG_HEAD_HDR_KEY "zlog.head.header"
#define ZLOG_VIEW_KEY_PREFIX "zlog.head.view."
#define ZLOG_DATA_HDR_KEY "zlog.data.header"
#define ZLOG_ENTRY_KEY_PREFIX "zlog.data.entry."

namespace cls_zlog {

static inline std::string u64tostr(uint64_t value,
    const std::string& prefix)
{
  std::stringstream ss;
  ss << prefix << std::setw(20) << std::setfill('0') << value;
  return ss.str();
}

class LogObjectHeader {
 public:
  explicit LogObjectHeader(cls_method_context_t hctx) :
    hctx_(hctx)
  {}

  int read() {
    ceph::bufferlist bl;
    int ret = cls_cxx_getxattr(hctx_, ZLOG_DATA_HDR_KEY, &bl);
    if (ret < 0) {
      // ENODATA means the object exists without a header. This would be a
      // violation of our basic protocol assumptions. Return an error value that
      // we won't catch. ENOENT is returned.
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

    return 0;
  }

  int write() {
    ceph::bufferlist bl;
    encode(bl, hdr_);
    return cls_cxx_setxattr(hctx_, ZLOG_DATA_HDR_KEY, &bl);
  }

  int epoch_guard(uint64_t epoch) {
    if (epoch < 1) {
      return -EINVAL;
    } else if (epoch < hdr_.epoch()) {
      return -ESPIPE;
    } else {
      return 0;
    }
  }

  uint64_t epoch() const {
    return hdr_.epoch();
  }

  void set_epoch(uint64_t epoch) {
    return hdr_.set_epoch(epoch);
  }

  boost::optional<uint64_t> max_pos() {
    if (hdr_.has_max_pos()) {
      return hdr_.max_pos();
    }
    return boost::none;
  }

  bool update_max_pos(uint64_t pos) {
    auto m = max_pos();
    if (!m || pos > *m) {
      hdr_.set_max_pos(pos);
      return true;
    }
    return false;
  }

  void set_omap_max_size(int32_t size) {
    hdr_.set_omap_max_size(size);
  }

  boost::optional<uint32_t> omap_max_size() const {
    if (hdr_.omap_max_size() >= 0) {
      return hdr_.omap_max_size();
    }
    return boost::none;
  }

 private:
  cls_method_context_t hctx_;
  zlog_ceph_proto::LogObjectHeader hdr_;
};

class LogEntry {
 public:
  LogEntry(cls_method_context_t hctx, uint64_t pos) :
    entry_key_(u64tostr(pos, ZLOG_ENTRY_KEY_PREFIX)),
    exists_(boost::none),
    hctx_(hctx)
  {}

  int read() {
    assert(!initialized());
    ceph::bufferlist bl;
    int ret = cls_cxx_map_get_val(hctx_, entry_key_, &bl);
    if (ret < 0) {
      if (ret == -ENOENT) {
        exists_ = false;
        return 0;
      }
      return ret;
    }
    if (!decode(bl, &entry_)) {
      CLS_ERR("ERROR: LogEntry::read decode failed");
      return -EIO;
    }
    exists_ = true;
    return 0;
  }

  int write() {
    ceph::bufferlist bl;
    encode(bl, entry_);
    return cls_cxx_map_set_val(hctx_, entry_key_, &bl);
  }

  bool exists() const {
    assert(initialized());
    return *exists_;
  }

  bool invalid() const {
    assert(exists());
    return entry_.invalid();
  }

  void invalidate() {
    entry_.set_invalid(true);
  }

  int set_data(const std::string& data,
      boost::optional<uint32_t> omap_max_size) {
    assert(!entry_.has_data());
    assert(!entry_.has_offset());
    assert(!entry_.has_length());

    if (omap_max_size && data.size() >= *omap_max_size) {
      // TODO: track object size in header?
      uint64_t obj_size;
      int ret = cls_cxx_stat(hctx_, &obj_size, NULL);
      if (ret < 0) {
        CLS_ERR("ERROR: set_data(): stat failed %d", ret);
        return ret;
      }

      // TODO: pad to align entry ios?
      // TODO: enforce a maximum size?
      entry_.set_offset(obj_size);
      entry_.set_length(data.size());

      ceph::bufferlist bl;
      bl.append(data.data(), data.size());
      ret = cls_cxx_write(hctx_, entry_.offset(),
          entry_.length(), &bl);
      if (ret < 0) {
        CLS_ERR("ERROR: set_data(): write failed %d", ret);
      }
      return ret;
    } else {
      entry_.set_data(data);
      return 0;
    }
  }

  int read(ceph::bufferlist *out) {
    assert(exists());
    if (entry_.has_data()) {
      if (entry_.has_offset() || entry_.has_length()) {
        return -EIO;
      }
      out->append(entry_.data());
      return 0;
    } else {
      if (!entry_.has_offset() || !entry_.has_length()) {
        return -EIO;
      }
      return cls_cxx_read(hctx_, entry_.offset(), entry_.length(), out);
    }
  }

 private:
  const std::string entry_key_;

  boost::optional<bool> exists_;
  bool initialized() const {
    return exists_ != boost::none;
  }

  cls_method_context_t hctx_;

  zlog_ceph_proto::LogEntry entry_;
};

/*
 * A head object contains log metadata including log views.
 */
class HeadObject {
 public:
  explicit HeadObject(cls_method_context_t hctx) :
    hctx_(hctx)
  {}

  HeadObject(cls_method_context_t hctx,
      zlog_ceph_proto::HeadObjectHeader hdr) :
    hctx_(hctx),
    hdr_(hdr)
  {}

  int initialize() {
    ceph::bufferlist bl;
    int ret = cls_cxx_getxattr(hctx_, ZLOG_HEAD_HDR_KEY, &bl);
    if (ret < 0) {
      // ENODATA means the object exists, but the key doesn't exist. This is
      // reported as EIO to indicate a protocol violation: the head object
      // should have been initialized.
      if (ret == -ENODATA) {
        CLS_ERR("ERROR: head object not initialized");
        return -EIO;
      }
      return ret;
    }
    if (!decode(bl, &hdr_)) {
      CLS_ERR("ERROR: decoding header");
      return -EIO;
    }
    return 0;
  }

  int finalize() {
    ceph::bufferlist bl;
    encode(bl, hdr_);
    return cls_cxx_setxattr(hctx_, ZLOG_HEAD_HDR_KEY, &bl);
  }

  uint64_t epoch() const {
    return hdr_.epoch();
  }

  int set_epoch(uint64_t epoch) {
    const uint64_t required_epoch = hdr_.epoch() + 1;
    if (epoch == required_epoch) {
      hdr_.set_epoch(epoch);
      return 0;
    } else if (epoch > required_epoch) {
      return -EINVAL;
    }
    return -ESPIPE;
  }

  int write_view(const std::string& data) {
    const auto key = view_key(hdr_.epoch());
    ceph::bufferlist bl;
    bl.append(data);
    return cls_cxx_map_set_val(hctx_, key, &bl);
  }

  int read_view(uint64_t epoch, ceph::bufferlist *bl) const {
    const auto key = view_key(epoch);
    return cls_cxx_map_get_val(hctx_, key, bl);
  }

 private:
  inline std::string view_key(uint64_t epoch) const {
    return u64tostr(epoch, ZLOG_VIEW_KEY_PREFIX);
  }

  cls_method_context_t hctx_;
  zlog_ceph_proto::HeadObjectHeader hdr_;
};

}
