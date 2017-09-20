#pragma once
#include "zlog/backend.h"

#ifdef __cplusplus
#include <rados/librados.hpp>
#include <iostream>

class CephBackend : public Backend {
 public:
  explicit CephBackend(librados::IoCtx *ioctx);

  std::string pool() override {
    return pool_;
  }

  int CreateLog(const std::string& name,
      const std::string& initial_view) override;

  int OpenLog(const std::string& name,
      std::string& hoid, std::string& prefix) override;

  int ReadViews(const std::string& hoid, uint64_t epoch,
      std::map<uint64_t, std::string>& views) override;

  int ProposeView(const std::string& hoid,
      uint64_t epoch, const std::string& view) override;

  int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data) override;

  int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position) override;

  int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position) override;

  int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position) override;

  int Seal(const std::string& oid,
      uint64_t epoch) override;

  int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos, bool *empty) override;

  int AioWrite(const std::string& oid, uint64_t epoch,
      uint64_t position, const Slice& data, void *arg,
      std::function<void(void*, int)> callback) override;

  int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data, void *arg,
      std::function<void(void*, int)> callback) override;

 private:
  struct AioContext {
    librados::AioCompletion *c;
    void *arg;
    std::function<void(void*, int)> cb;
    ceph::bufferlist bl;
    std::string *data;
  };

  librados::IoCtx *ioctx_;
  std::string pool_;

  static void aio_safe_cb_append(librados::completion_t cb, void *arg);
  static void aio_safe_cb_read(librados::completion_t cb, void *arg);

  static std::string LinkObjectName(const std::string& name);

  int CreateLinkObject(const std::string& name,
      const std::string& hoid);
  int InitHeadObject(const std::string& hoid, const std::string& prefix);
};

extern "C" {
#endif

int zlog_create_ceph_backend(rados_ioctx_t ioctx, zlog_backend_t *backend);
int zlog_destroy_ceph_backend(zlog_backend_t backend);

#ifdef __cplusplus
}
#endif
