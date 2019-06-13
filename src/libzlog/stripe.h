#pragma once
#include <cassert>
#include <string>
#include <vector>

namespace zlog {

class Stripe {
 public:
  Stripe(const std::string& prefix,
      uint64_t stripe_id,
      uint32_t width,
      uint64_t min_position,
      uint64_t max_position) :
    prefix_(prefix),
    stripe_id_(stripe_id),
    width_(width),
    min_position_(min_position),
    max_position_(max_position),
    oids_(make_oids())
  {}

  uint64_t min_position() const {
    return min_position_;
  }

  uint64_t max_position() const {
    return max_position_;
  }

  uint32_t width() const {
    return width_;
  }

  const std::vector<std::string>& oids() const {
    return oids_;
  }

  static std::string make_oid(const std::string& prefix,
      uint64_t stripe_id, uint32_t width, uint64_t position);

 private:
  static std::string make_oid(const std::string& prefix,
      uint64_t stripe_id, uint32_t index);

  std::vector<std::string> make_oids();

  const std::string prefix_;
  const uint64_t stripe_id_;
  const uint32_t width_;
  const uint64_t min_position_;
  const uint64_t max_position_;
  const std::vector<std::string> oids_;
};

class MultiStripe {
 public:
  MultiStripe(const std::string& prefix,
      uint64_t base_id,
      uint32_t width,
      uint32_t slots,
      uint64_t min_position,
      uint64_t instances,
      uint64_t max_position) :
    prefix_(prefix),
    base_id_(base_id),
    width_(width),
    slots_(slots),
    min_position_(min_position),
    instances_(instances),
    max_position_(max_position)
  {
    assert(!prefix_.empty());
    assert(base_id_ >= 0);
    assert(width_ > 0);
    assert(slots_ > 0);
    assert(min_position_ >= 0);
    assert(instances_ > 0);
    assert(max_position_ > 0);
  }

  std::string map(uint64_t stripe_id, uint64_t position) const {
    return Stripe::make_oid(prefix_, stripe_id, width_, position);
  }

  uint64_t base_id() const {
    return base_id_;
  }

  uint64_t max_stripe_id() const {
    return base_id_ + instances_ - 1;
  }

  uint64_t max_position() const {
    return max_position_;
  }

  uint32_t width() const {
    return width_;
  }

  uint32_t slots() const {
    return slots_;
  }

  uint32_t instances() const {
    return instances_;
  }

  Stripe stripe_by_id(uint64_t stripe_id) const {
    assert(base_id() <= stripe_id);
    assert(stripe_id <= max_stripe_id());
    const uint64_t stripe_offset = stripe_id - base_id();
    const uint64_t entries_per_stripe = (uint64_t)width_ * slots_;
    const uint64_t min_pos = min_position_ + (stripe_offset * entries_per_stripe);
    const uint64_t max_pos = min_pos + entries_per_stripe - 1;
    assert(stripe_offset < instances_);
    assert(entries_per_stripe > 0);
    assert(min_pos >= min_position_);
    assert(max_pos <= max_position_);
    return Stripe(
        prefix_,
        stripe_id,
        width_,
        min_pos,
        max_pos);
  }

  void extend() {
    instances_++;
    max_position_ += (uint64_t)width_ * slots_;
  }

 private:
  const std::string prefix_;
  const uint64_t base_id_;
  const uint32_t width_;
  const uint32_t slots_;
  const uint64_t min_position_;
  uint64_t instances_;
  uint64_t max_position_;
};

}
