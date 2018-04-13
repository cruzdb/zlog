#pragma once
#include <map>
#include <mutex>
#include <sstream>
#include <boost/optional.hpp>
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
    uint32_t width;
    uint32_t max_size;
    std::string oid;
  };

  Striper(const std::string& prefix) :
    prefix_(prefix)
  {}

  static zlog_proto::View InitViewData(uint32_t width,
      uint32_t entries_per_object);

  std::pair<uint64_t, zlog_proto::View> LatestView() const;

  // Add the serialized view data for an epoch
  int Add(uint64_t epoch, const std::string& data);

  bool Empty() const {
    std::lock_guard<std::mutex> l(lock_);
    return views_.empty();
  }

  StripeInfo GetCurrent() const {
    std::lock_guard<std::mutex> l(lock_);
    assert(!views_.empty());
    auto latest = views_.rbegin();
    return StripeInfo{epoch_,
      latest->first,
      latest->second.width(),
      latest->second.oids()};
  }

  uint64_t Epoch() const {
    std::lock_guard<std::mutex> l(lock_);
    assert(!views_.empty());
    return epoch_;
  }

  boost::optional<Mapping> MapPosition(uint64_t position) const;

 private:
  class ViewEntry {
   public:
    ViewEntry(const std::string& prefix, uint64_t epoch, uint32_t width,
        uint64_t maxpos, uint32_t max_size) :
      width_(width), maxpos_(maxpos), max_size_(max_size)
    {
      for (auto i = 0u; i < width_; i++) {
        std::stringstream oid;
        oid << prefix << "." << epoch << "." << i;
        oids_.push_back(oid.str());
      }
    }

    uint32_t width() const {
      return width_;
    }

    uint64_t maxpos() const {
      return maxpos_;
    }

    std::string map(uint64_t position) const {
      auto index = position % width_;
      assert(index < oids_.size());
      return oids_[index];
    }

    std::vector<std::string> oids() const {
      return oids_;
    }

    uint32_t max_size() const {
      return max_size_;
    }

   private:
    uint32_t width_;
    uint64_t maxpos_;
    uint32_t max_size_;
    std::vector<std::string> oids_;
  };

  mutable std::mutex lock_;
  const std::string prefix_;

  // min-pos(inclusive) -> entry
  std::map<uint64_t, ViewEntry> views_;
  zlog_proto::View latest_view_;
  uint64_t epoch_;
};
