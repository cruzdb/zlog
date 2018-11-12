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

  int uniqueId(const std::string& hoid, uint64_t *id) override;

  int CreateLog(const std::string& name, const std::string& view,
      std::string *hoid_out, std::string *prefix_out) override;

  int OpenLog(const std::string& name, std::string *hoid,
      std::string *prefix_out) override;

  int ListLinks(std::vector<std::string> &loids_out) override;

  int ListHeads(std::vector<std::string> &ooids_out) override;

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
      uint64_t position) override;

  int Seal(const std::string& oid,
      uint64_t epoch) override;

  int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos, bool *empty) override;

 private:
  struct LinkObject {
    std::string hoid;
  };

  // this is head object / hoid
  struct ProjectionObject {
    uint64_t epoch;
    std::string prefix;
    std::map<uint64_t, std::string> projections;
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

  bool startsWith(std::string s, std::string prefix) {
    return s.size() >= prefix.size() && std::equal(prefix.cbegin(), prefix.cend(), s.cbegin());
  }

 private:
  mutable std::mutex lock_;
  std::map<std::string, std::string> options_;
  std::map<std::string,
    boost::variant<LinkObject, ProjectionObject, LogObject>> objects_;
};

}
}
}
