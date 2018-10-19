#pragma once
#include <cerrno>
#include <sstream>
#include <string>
#include <boost/optional.hpp>
#include <rados/buffer.h>
#include <rados/objclass.h>
#include "storage/ceph/cls_zlog.pb.h"
#include "storage/ceph/protobuf_bufferlist_adapter.h"

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
    int ret = cls_cxx_getxattr(hctx_, log_hdr_key_, &bl);
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
    return cls_cxx_setxattr(hctx_, log_hdr_key_, &bl);
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

 private:
  const char *log_hdr_key_ = "zlog.data.header";
  cls_method_context_t hctx_;
  zlog_ceph_proto::LogObjectHeader hdr_;
};

class LogEntry {
 public:
  LogEntry(cls_method_context_t hctx, uint64_t pos) :
    entry_key_(u64tostr(pos, entry_prefix_)),
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

  void set_data(const std::string& data) {
    assert(!entry_.has_data());
    entry_.set_data(data);
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
  const char *entry_prefix_ = "zlog.data.entry.";
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
    int ret = cls_cxx_getxattr(hctx_, view_hdr_key_, &bl);
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
    return cls_cxx_setxattr(hctx_, view_hdr_key_, &bl);
  }

  uint64_t epoch() const {
    return hdr_.epoch();
  }

  int set_epoch(uint64_t epoch) {
    if (epoch == (hdr_.epoch() + 1)) {
      hdr_.set_epoch(epoch);
      return 0;
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
  const char *view_hdr_key_ = "zlog.head.header";
  const char *view_key_prefix_ = "zlog.head.view.";
  inline std::string view_key(uint64_t epoch) const {
    return u64tostr(epoch, view_key_prefix_);
  }

  cls_method_context_t hctx_;
  zlog_ceph_proto::HeadObjectHeader hdr_;
};

}
