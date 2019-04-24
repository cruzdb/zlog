#pragma once
#include <iostream>
#include <boost/optional.hpp>
#include <rados/librados.hpp>
#include "zlog/backend.h"

namespace zlog {
namespace storage {
namespace ceph {

class CephBackend : public Backend {
 public:
  CephBackend();
  ~CephBackend();

  std::map<std::string, std::string> meta() override;

  int Initialize(librados::IoCtx *ioctx);
  int Initialize(const std::map<std::string, std::string>& opts) override;

  int uniqueId(const std::string& hoid, uint64_t *id) override;

  int CreateLog(const std::string& name, const std::string& view,
      std::string *hoid_out, std::string *prefix_out) override;

  int OpenLog(const std::string& name, std::string *hoid_out,
      std::string *prefix_out) override;

  int ReadViews(const std::string& hoid,
      uint64_t epoch, uint32_t max_views,
      std::map<uint64_t, std::string> *views_out) override;

  int ProposeView(const std::string& hoid,
      uint64_t epoch, const std::string& view) override;

  int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data) override;

  int Write(const std::string& oid, const std::string& data,
      uint64_t epoch, uint64_t position) override;

  int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position) override;

  int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position, bool trim_limit, bool trim_full) override;

  int Seal(const std::string& oid,
      uint64_t epoch) override;

  int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos, bool *empty) override;

  int Stat(const std::string& oid, size_t *size) override;

 private:
  std::map<std::string, std::string> options;

  librados::Rados *cluster_;
  librados::IoCtx *ioctx_;
  std::string pool_;

  // boost::none -> always use omap
  //           0 -> always use bytestream
  //         > 0 -> use omap when entry < max size
  boost::optional<uint32_t> omap_max_size_;

  static std::string LinkObjectName(const std::string& name);

  int CreateLinkObject(const std::string& name,
      const std::string& hoid);
  int InitHeadObject(const std::string& hoid, const std::string& prefix);
  int RegisterCephApp();
};

}
}
}
