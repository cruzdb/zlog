#ifndef ZLOG_INCLUDE_ZLOG_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_BACKEND_H
#include "zlog/slice.h"
#include "proto/zlog.pb.h"

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

  /*
   * TODO: this is used to provide the rados pool name when composing requests
   * to the sequencer. this rados specific, and needs to be factored out
   * somehow.
   */
  virtual std::string pool() = 0;

  /*
   *
   */
  virtual int Exists(const std::string& oid) = 0;

  /*
   *
   */
  virtual int CreateHeadObject(const std::string& oid,
      const zlog_proto::MetaLog& data) = 0;

  /*
   *
   */
  virtual int SetProjection(const std::string& oid, uint64_t epoch,
      const zlog_proto::MetaLog& data) = 0;

  /*
   *
   */
  virtual int LatestProjection(const std::string& oid,
      uint64_t *epoch, zlog_proto::MetaLog& data) = 0;

  /*
   *
   */
  virtual int Seal(const std::string& oid, uint64_t epoch) = 0;

  /*
   *
   */
  virtual int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos) = 0;

  /*
   *
   */
  virtual int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position) = 0;

  /*
   *
   */
  virtual int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data) = 0;

  /*
   *
   */
  virtual int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position) = 0;

  /*
   *
   */
  virtual int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position) = 0;

  /*
   *
   */
  virtual int AioAppend(const std::string& oid, uint64_t epoch,
      uint64_t position, const Slice& data, void *arg,
      std::function<void(void*, int)> callback) = 0;

  /*
   *
   */
  virtual int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data, void *arg,
      std::function<void(void*, int)> callback) = 0;
};

#endif
