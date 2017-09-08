#pragma once
// TODO
//  - remove ceph-specific pool method
#include <cstdint>
#include <functional>
#include <string>

#include "zlog/slice.h"
#include "proto/zlog.pb.h"

// TODO
//  - those return values!
//
class Backend {
 public:
  enum {
    //ZLOG_OK = 9823098,
    ZLOG_OK = 0,
    ZLOG_STALE_EPOCH,
    ZLOG_READ_ONLY,
    ZLOG_NOT_WRITTEN,
    ZLOG_INVALIDATED,
    ZLOG_INVALID_EPOCH,
  };

  virtual ~Backend() {}

  virtual int CreateLog(const std::string& name,
      const std::string& initial_view) = 0;

  virtual int OpenLog(const std::string& name,
      std::string& prefix) = 0;

  virtual int ReadViews(const std::string& hoid,
      uint64_t epoch, std::map<uint64_t, std::string>& views) = 0;

  virtual int ProposeView(const std::string& hoid,
      uint64_t epoch, const std::string& view) = 0;

  // Write data into a log position.
  virtual int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position) = 0;

  virtual int AioWrite(const std::string& oid, uint64_t epoch,
      uint64_t position, const Slice& data, void *arg,
      std::function<void(void*, int)> callback) = 0;

  // Read the contents of a log position.
  virtual int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data) = 0;

  virtual int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data, void *arg,
      std::function<void(void*, int)> callback) = 0;

  // Invalidate a log position.
  virtual int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position) = 0;

  // Force invalidate a log position.
  virtual int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position) = 0;

  virtual int Seal(const std::string& oid, uint64_t epoch) = 0;

  virtual int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos, bool *empty) = 0;

  virtual std::string pool() = 0;
};
