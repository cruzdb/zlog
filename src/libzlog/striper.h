#pragma once
#include <map>
#include <mutex>
#include "proto/zlog.pb.h"

class Striper {
 public:
  struct StripeInfo {
    uint64_t epoch;
    uint64_t minpos;
    uint32_t width;
    std::vector<std::string> oids;
  };

  struct Mapping {
    uint64_t epoch;
    std::string oid;
  };

  Striper(const std::string& prefix) :
    prefix_(prefix)
  {}

  static zlog_proto::View InitViewData(uint32_t width);
  zlog_proto::View LatestView() const;

  // Add the serialized view data for an epoch
  int Add(uint64_t epoch, const std::string& data);

  bool Empty() const {
    std::lock_guard<std::mutex> l(lock_);
    return views_.empty();
  }

  StripeInfo GetCurrent() const {
    std::lock_guard<std::mutex> l(lock_);
    assert(!views_.empty());
    return StripeInfo{epoch_,
      views_.rbegin()->first,
      views_.rbegin()->second,
      oids_};
  }

  uint64_t Epoch() const {
    std::lock_guard<std::mutex> l(lock_);
    assert(!views_.empty());
    return epoch_;
  }

  Mapping MapPosition(uint64_t position) const;

 private:
  mutable std::mutex lock_;

  const std::string prefix_;

  // position(incl):width
  std::map<uint64_t, uint32_t> views_;
  std::vector<std::string> oids_;
  zlog_proto::View latest_view_;
  uint64_t epoch_;

  void GenerateObjects();
};
