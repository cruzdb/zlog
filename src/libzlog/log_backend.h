#pragma once
#include <iostream>
#include <sstream>
#include "include/zlog/backend.h"

namespace zlog {

// in future reprsent oid as (stripe id, index) and then do caching in here??
class LogBackend final {
 public:
  LogBackend(std::shared_ptr<Backend> backend,
      const std::string& hoid,
      const std::string& prefix) :
    backend_(backend),
    hoid_(hoid),
    prefix_(prefix)
  {}

 public:
  std::shared_ptr<Backend> backend() const {
    return backend_;
  }

  std::string hoid() const {
    return hoid_;
  }

  std::string prefix() const {
    return prefix_;
  }

 public:
  int ReadViews(uint64_t epoch, uint32_t max_views,
      std::map<uint64_t, std::string> *views_out) const {
    return backend_->ReadViews(hoid_, epoch, max_views, views_out);
  }

  int ProposeView(uint64_t epoch, const std::string& view) const {
    return backend_->ProposeView(hoid_, epoch, view);
  }

  int uniqueId(uint64_t *id_out) const {
    return backend_->uniqueId(hoid_, id_out);
  }

  int Read(const std::string& oid, uint64_t epoch, uint64_t position,
      std::string *data_out) const {
    std::stringstream prefixed_oid;
    prefixed_oid << prefix_ << "." << oid;
    return backend_->Read(prefixed_oid.str(), epoch, position, data_out);
  }

  int Write(const std::string& oid, const std::string& data, uint64_t epoch,
      uint64_t position) const {
    std::stringstream prefixed_oid;
    prefixed_oid << prefix_ << "." << oid;
    return backend_->Write(prefixed_oid.str(), data, epoch, position);
  }

  int Fill(const std::string& oid, uint64_t epoch, uint64_t position) const {
    std::stringstream prefixed_oid;
    prefixed_oid << prefix_ << "." << oid;
    return backend_->Fill(prefixed_oid.str(), epoch, position);
  }

  int Trim(const std::string& oid, uint64_t epoch, uint64_t position,
      bool trim_limit = false, bool trim_full = false) const {
    std::stringstream prefixed_oid;
    prefixed_oid << prefix_ << "." << oid;
    return backend_->Trim(prefixed_oid.str(), epoch, position, trim_limit,
        trim_full);
  }

  int Seal(const std::string& oid, uint64_t epoch) const {
    std::stringstream prefixed_oid;
    prefixed_oid << prefix_ << "." << oid;
    return backend_->Seal(prefixed_oid.str(), epoch);
  }

  int MaxPos(const std::string& oid, uint64_t epoch, uint64_t *pos_out,
      bool *empty_out) const {
    std::stringstream prefixed_oid;
    prefixed_oid << prefix_ << "." << oid;
    return backend_->MaxPos(prefixed_oid.str(), epoch, pos_out, empty_out);
  }

  int Stat(const std::string& oid, size_t *size) const {
    std::stringstream prefixed_oid;
    prefixed_oid << prefix_ << "." << oid;
    return backend_->Stat(prefixed_oid.str(), size);
  }

 private:
  const std::shared_ptr<Backend> backend_;
  const std::string hoid_;
  const std::string prefix_;
};

}
