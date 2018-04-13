#pragma once
#include <iostream>
#include <rados/librados.hpp>
#include "zlog/backend.h"

namespace zlog {
namespace storage {
namespace ceph {

class CephBackend : public Backend {
 public:
  CephBackend();
  explicit CephBackend(librados::IoCtx *ioctx);

  ~CephBackend();

  std::map<std::string, std::string> meta() override;

  int Initialize(const std::map<std::string, std::string>& opts) override;

  int CreateLog(const std::string& name,
      const std::string& initial_view) override;

  int OpenLog(const std::string& name,
      std::string& hoid, std::string& prefix) override;

  int ReadViews(const std::string& hoid, uint64_t epoch,
      std::map<uint64_t, std::string>& views) override;

  int ProposeView(const std::string& hoid,
      uint64_t epoch, const std::string& view) override;

  int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      std::string *data) override;

  int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position, uint32_t stride,
      uint32_t max_size) override;

  int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size) override;

  int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size) override;

  int Seal(const std::string& oid,
      uint64_t epoch) override;

  int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos, bool *empty) override;

  int AioWrite(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      const Slice& data, void *arg,
      std::function<void(void*, int)> callback) override;

  int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      std::string *data, void *arg,
      std::function<void(void*, int)> callback) override;

 private:
  struct AioContext {
    librados::AioCompletion *c;
    void *arg;
    std::function<void(void*, int)> cb;
    ::ceph::bufferlist bl;
    std::string *data;
  };

  std::map<std::string, std::string> options;

  librados::Rados *cluster_;
  librados::IoCtx *ioctx_;
  std::string pool_;

  static void aio_safe_cb_append(librados::completion_t cb, void *arg);
  static void aio_safe_cb_read(librados::completion_t cb, void *arg);

  static std::string LinkObjectName(const std::string& name);

  int CreateLinkObject(const std::string& name,
      const std::string& hoid);
  int InitHeadObject(const std::string& hoid, const std::string& prefix);
};

}
}
}
