#pragma once
#include <vector>
#include <sstream>
#include <iostream>
#include <memory>
#include <mutex>
#include <boost/variant.hpp>
#include <unordered_map>
#include "zlog/backend.h"

namespace zlog {
namespace storage {
namespace ram {

class RAMBackend : public Backend {
 public:
  RAMBackend() :
    options_{{"scheme", "ram"}}
  {}

  ~RAMBackend();

  int Initialize(const std::map<std::string, std::string>& opts) override;

  std::map<std::string, std::string> meta() override;

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
  struct ProjectionObject {
    ProjectionObject() : latest_epoch(0) {}
    uint64_t latest_epoch;
    std::unordered_map<uint64_t, std::string> projections;
  };

  struct LogEntry {
    bool trimmed;
    bool invalidated;
    std::string data;
    LogEntry() : trimmed(false), invalidated(false) {}
  };

  struct LogObject {
    uint64_t epoch;
    uint64_t maxpos;
    std::unordered_map<uint64_t, LogEntry> entries;
    LogObject() : epoch(0), maxpos(0) {}
  };

 private:
  int CheckEpoch(uint64_t epoch, const std::string& oid,
      bool eq, LogObject*& lobj);

 private:
  mutable std::mutex lock_;
  std::map<std::string, std::string> options_;
  std::map<std::string,
    boost::variant<ProjectionObject, LogObject>> objects_;
};

}
}
}
