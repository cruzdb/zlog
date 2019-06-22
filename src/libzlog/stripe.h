#pragma once
#include <cassert>
#include <string>
#include <vector>
#include "libzlog/zlog_generated.h"

namespace zlog {

// Stripe describes the storage layout of a contiguous range of log positions.
// It also serves as the granularity at which log configuration changes are
// managed. Because a log may have an unbounded number of stripes it is not
// feasible to explicitly represent each stripe in memory. Therefore, the
// MultiStripe object below is used to manage a compact representation of
// stripes.
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
  {
    assert(!prefix_.empty());
    assert(stripe_id_ >= 0);
    assert(width_ > 0);
    if (stripe_id_ > 0) {
      assert(min_position_ > 0);
      assert(max_position_ > 0);
    } else {
      assert(min_position_ >= 0);
      assert(max_position_ >= 0);
    }
    assert(min_position_ <= max_position_);
  }

 public:
  static std::string make_oid(const std::string& prefix,
      uint64_t stripe_id, uint32_t width, uint64_t position);

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

 private:
  // index is the pre-computed value: position % stripe-width
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

// MultiStripe is a compact representation of adjancent Stripe objects in the
// log position address space. Two adjacent Stripe objects can be represented by
// a single MultiStripe object if they are compatible---they have the same
// configuration (e.g. width and number of slots).
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
    assert(instances_ > 0);
    if (base_id_ > 0) {
      assert(min_position_ > 0);
      assert(max_position_ > 0);
    } else {
      assert(min_position_ >= 0);
      if (instances_ > 1) {
        assert(max_position_ > 0);
      } {
        assert(max_position_ >= 0);
      }
    }
    assert(min_position_ <= max_position_);
  }

 public:
  // construct a MultiStripe from a flatbuffer
  static MultiStripe decode(const std::string& prefix,
      const flatbuffers::VectorIterator<
        flatbuffers::Offset<zlog::fbs::MultiStripe>,
        const zlog::fbs::MultiStripe*>& it);

  // encode this MultiStripe object into a flatbuffer
  flatbuffers::Offset<zlog::fbs::MultiStripe> encode(
          flatbuffers::FlatBufferBuilder& fbb) const;

 public:
  // given a stripe id and a position, compute the name of the object that the
  // position maps to. the stripe id _must_ be represented by this MultiStripe.
  std::string map(uint64_t stripe_id, uint64_t position) const {
    assert(base_id_ <= stripe_id);
    assert(stripe_id <= max_stripe_id());
    return Stripe::make_oid(prefix_, stripe_id, width_, position);
  }

  // the (fixed) smallest stripe id represented by this MultiStripe
  uint64_t base_id() const {
    return base_id_;
  }

  // the maximum stripe id represented by this MultiStripe. this is fixed per
  // instance of the MultiStripe, but increases when a new MultiStripe is
  // created by expanding an existing instance.
  uint64_t max_stripe_id() const {
    return base_id_ + instances_ - 1;
  }

  uint64_t min_position() const {
    return min_position_;
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

  // construct a new MultiStripe by extending the current MultiStripe to
  // represent one additional adjacent Stripe.
  MultiStripe extend() const {
    return MultiStripe(
        prefix_,
        base_id_,
        width_,
        slots_,
        min_position_,
        instances_ + 1,
        max_position_ + (uint64_t)width_ * slots_);
  }

  // construct a stripe object given its stripe id. this is an expensive
  // operation since it pre-computes all of the object names.
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

 private:
  const std::string prefix_;
  const uint64_t base_id_;
  const uint32_t width_;
  const uint32_t slots_;
  const uint64_t min_position_;
  const uint64_t instances_;
  const uint64_t max_position_;
};

}
