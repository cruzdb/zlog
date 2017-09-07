// TODO: change file name
#pragma once
#include <map>
#include <mutex>
#include "proto/zlog.pb.h"

class Striper {
 public:
  struct StripeInfo {
    uint64_t epoch;
    uint64_t maxpos;
    uint32_t width;
  };

  struct Mapping {
    uint64_t epoch;
    std::string oid;
  };

  Striper(const std::string& prefix) :
    prefix_(prefix)
  {}

  static std::string InitViewData(uint32_t width);
  static std::string BuildViewData(uint64_t pos, uint32_t width);
  std::string NewResumeViewData() const;
  std::string NewViewData(uint64_t pos) const;

  // Add the serialized view data for an epoch
  int Add(uint64_t epoch, const std::string& data);

  bool Empty() const {
    std::lock_guard<std::mutex> l(lock_);
    return views_.empty();
  }

  StripeInfo GetCurrent() const {
    std::lock_guard<std::mutex> l(lock_);
    return StripeInfo{epoch_,
      views_.rbegin()->first,
      views_.rbegin()->second};
  }

  uint64_t Epoch() const {
    std::lock_guard<std::mutex> l(lock_);
    assert(!views_.empty());
    return epoch_;
  }

  std::pair<uint64_t, std::vector<std::string>>
  StripeObjects() {
    std::lock_guard<std::mutex> l(lock_);
    assert(!views_.empty());
    return std::make_pair(epoch_, oids_);
  }

  Mapping MapPosition(uint64_t position) const;

 private:
  mutable std::mutex lock_;

  const std::string prefix_;

  // position(incl):width
  std::map<uint64_t, uint32_t> views_;
  std::vector<std::string> oids_;
  uint64_t epoch_;

  void GenerateObjects();
};
