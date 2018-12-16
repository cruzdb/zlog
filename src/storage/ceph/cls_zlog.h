#pragma once
#include <cerrno>
#include <sstream>
#include <string>
#include <boost/optional.hpp>
#include <rados/buffer.h>
#include <rados/objclass.h>
#include "storage/ceph/cls_zlog_generated.h"
#include "fbs_helper.h"

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
    hctx_(hctx),
    empty_(true),
    omap_max_size_(-1)
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

    auto header = fbs_bl_decode<fbs::LogObjectHeader>(&bl);
    if (!header) {
      CLS_ERR("ERROR: read_header(): failed to decode header");
      return -EIO;
    }

    epoch_ = header->epoch();
    empty_ = header->empty();
    max_pos_ = header->max_pos();
    omap_max_size_ = header->omap_max_size();

    return 0;
  }

  int write() {
    flatbuffers::FlatBufferBuilder fbb;
    auto header = fbs::CreateLogObjectHeader(fbb, epoch_,
        empty_, max_pos_, omap_max_size_);
    fbb.Finish(header);

    ceph::bufferlist bl;
    fbs_bl_encode(fbb, &bl);

    return cls_cxx_setxattr(hctx_, ZLOG_DATA_HDR_KEY, &bl);
  }

  int epoch_guard(uint64_t epoch) {
    if (epoch < 1) {
      return -EINVAL;
    } else if (epoch < epoch_) {
      return -ESPIPE;
    } else {
      return 0;
    }
  }

  uint64_t epoch() const {
    return epoch_;
  }

  void set_epoch(uint64_t epoch) {
    epoch_ = epoch;
  }

  boost::optional<uint64_t> max_pos() {
    if (!empty_) {
      return max_pos_;
    }
    return boost::none;
  }

  bool update_max_pos(uint64_t pos) {
    auto m = max_pos();
    if (!m || pos > *m) {
      max_pos_ = pos;
      empty_ = false;
      return true;
    }
    return false;
  }

  void set_omap_max_size(int32_t size) {
    omap_max_size_ = size;
  }

  boost::optional<uint32_t> omap_max_size() const {
    if (omap_max_size_ >= 0) {
      return omap_max_size_;
    }
    return boost::none;
  }

 private:
  cls_method_context_t hctx_;
  uint64_t epoch_;
  bool empty_;
  uint64_t max_pos_;
  int32_t omap_max_size_;
};

class LogEntry {
 public:
  LogEntry(cls_method_context_t hctx, uint64_t pos) :
    entry_key_(u64tostr(pos, ZLOG_ENTRY_KEY_PREFIX)),
    exists_(boost::none),
    hctx_(hctx),
    invalid_(false),
    offset_(0),
    length_(0)
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

    auto entry = fbs_bl_decode<fbs::LogEntry>(&bl);
    if (!entry) {
      CLS_ERR("ERROR: LogEntry::read decode failed");
      return -EIO;
    }

    invalid_ = entry->invalid();
    bytestream_ = entry->bytestream();
    if (entry->data()) {
      data_ = std::string(entry->data()->begin(), entry->data()->end());
    }
    offset_ = entry->offset();
    length_ = entry->length();

    exists_ = true;

    return 0;
  }

  int write() {
    flatbuffers::FlatBufferBuilder fbb(data_.size());
    auto data = fbb.CreateVector((uint8_t*)data_.c_str(), data_.size());
    auto entry = fbs::CreateLogEntry(fbb,
        invalid_,
        bytestream_,
        data,
        offset_,
        length_);
    fbb.Finish(entry);

    ceph::bufferlist bl;
    fbs_bl_encode(fbb, &bl);

    return cls_cxx_map_set_val(hctx_, entry_key_, &bl);
  }

  bool exists() const {
    assert(initialized());
    return *exists_;
  }

  bool invalid() const {
    assert(exists());
    return invalid_;
  }

  void invalidate() {
    invalid_ = true;
  }

  int set_data(const std::string& data,
      boost::optional<uint32_t> omap_max_size) {
    assert(offset_ == 0);
    assert(length_ == 0);
    assert(data_.empty());

    if (omap_max_size && data.size() >= *omap_max_size) {
      uint64_t obj_size;
      int ret = cls_cxx_stat(hctx_, &obj_size, NULL);
      if (ret < 0) {
        CLS_ERR("ERROR: set_data(): stat failed %d", ret);
        return ret;
      }

      offset_ = obj_size;
      length_ = data.size();

      ceph::bufferlist bl;
      bl.append(data.data(), data.size());
      ret = cls_cxx_write(hctx_, offset_, length_, &bl);
      if (ret < 0) {
        CLS_ERR("ERROR: set_data(): write failed %d", ret);
      }
      bytestream_ = true;
      return ret;
    } else {
      bytestream_ = false;
      data_ = data;
      return 0;
    }
  }

  int read(ceph::bufferlist *out) {
    assert(exists());
    if (bytestream_) {
      if (!data_.empty()) {
        CLS_ERR("ERROR: unexpected data");
        return -EIO;
      }
      if (length_ == 0) {
        // passing len=0 to read will return all object data
        return 0;
      }
      return cls_cxx_read(hctx_, offset_, length_, out);
    } else {
      if (offset_ != 0 || length_ != 0) {
        CLS_ERR("ERROR: unexpected offset / length");
        return -EIO;
      }
      out->append(data_.c_str(), data_.size());
      return 0;
    }
  }

 private:
  const std::string entry_key_;

  boost::optional<bool> exists_;
  bool initialized() const {
    return exists_ != boost::none;
  }

  cls_method_context_t hctx_;

  bool invalid_;
  bool bytestream_;
  std::string data_;
  uint32_t offset_;
  uint32_t length_;
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
      uint64_t epoch, std::string prefix) :
    hctx_(hctx),
    epoch_(epoch),
    prefix_(prefix)
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

    auto header = fbs_bl_decode<fbs::HeadObjectHeader>(&bl);
    if (!header) {
      CLS_ERR("ERROR: decoding header");
      return -EIO;
    }

    if (!header->prefix()) {
      CLS_ERR("ERROR: prefix undefined");
      return -EIO;
    }

    prefix_ = header->prefix()->str();
    if (prefix_.empty()) {
      CLS_ERR("ERROR: empty prefix");
      return -EIO;
    }

    epoch_ = header->epoch();

    return 0;
  }

  int finalize() {
    flatbuffers::FlatBufferBuilder fbb;
    auto header = fbs::CreateHeadObjectHeaderDirect(
        fbb, epoch_, prefix_.c_str());
    fbb.Finish(header);

    ceph::bufferlist bl;
    fbs_bl_encode(fbb, &bl);

    return cls_cxx_setxattr(hctx_, ZLOG_HEAD_HDR_KEY, &bl);
  }

  uint64_t epoch() const {
    return epoch_;
  }

  int set_epoch(uint64_t epoch) {
    const uint64_t required_epoch = epoch_ + 1;
    if (epoch == required_epoch) {
      epoch_ = epoch;
      return 0;
    } else if (epoch > required_epoch) {
      return -EINVAL;
    }
    return -ESPIPE;
  }

  int write_view(const std::string& data) {
    const auto key = view_key(epoch_);
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
  uint64_t epoch_;
  std::string prefix_;
};

}
