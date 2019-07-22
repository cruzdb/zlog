#pragma once
#include <atomic>
#include <boost/optional.hpp>
#include "libzlog/zlog_generated.h"
#include <nlohmann/json.hpp>

namespace zlog {

class Sequencer {
 public:
  explicit Sequencer(uint64_t epoch, uint64_t position) :
    epoch_(epoch),
    position_(position)
  {}

  uint64_t check_tail(bool next) {
    if (next) {
      return position_.fetch_add(1);
    } else {
      return position_.load();
    }
  }

  // TODO: why?
  uint64_t epoch() const {
    return epoch_;
  }

 private:
  const uint64_t epoch_;
  std::atomic<uint64_t> position_;
};

class SequencerConfig {
 public:
  SequencerConfig(uint64_t epoch, const std::string& token,
      uint64_t position) :
    epoch_(epoch),
    token_(token),
    position_(position)
  {}

 public:
  static boost::optional<SequencerConfig> decode(
      const zlog::fbs::Sequencer *seq);

  flatbuffers::Offset<zlog::fbs::Sequencer> encode(
      flatbuffers::FlatBufferBuilder& fbb) const;

  nlohmann::json dump() const;

 public:
  uint64_t epoch() const {
    return epoch_;
  }

  std::string token() const {
    return token_;
  }

  uint64_t position() const {
    return position_;
  }

  bool operator==(const SequencerConfig& other) const {
    return
      epoch_ == other.epoch_ &&
      token_ == other.token_ &&
      position_ == other.position_;
  }

 private:
  uint64_t epoch_;
  std::string token_;
  uint64_t position_;
};

}
