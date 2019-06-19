#pragma once
#include <atomic>
#include <boost/optional.hpp>

namespace zlog::fbs {
  class View;
}

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

  uint64_t epoch() const {
    return epoch_;
  }

 private:
  const uint64_t epoch_;
  std::atomic<uint64_t> position_;
};

struct SequencerConfig {
  uint64_t epoch;
  std::string secret;
  uint64_t position;

  static boost::optional<SequencerConfig> from_view(
      const zlog::fbs::View *view);
};

}
