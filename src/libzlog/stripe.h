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
    oids_(make_oids(prefix_, stripe_id_, width_))
  {
    assert(!prefix_.empty());
    assert(width_ > 0);

    // these restrictions aren't fundamental, but they happen to be true for the
    // current design.
    if (stripe_id_ > 0) {
      assert(min_position_ > 0);
    } else {
      assert(min_position_ == 0);
    }

    assert(min_position_ <= max_position_);

    // these relationships are true when we assume that the address space of a
    // stripe is always used / valid. that is, we don't cause part of a view
    // (e.g. the high end of the address range) to be remapped. this might not
    // hold in the future, but it does now for now.
    assert(max_position_ >= (min_position_ + width_ - 1));
    assert((max_position_ - min_position_ + 1) % width_ == 0);
  }

  Stripe(const Stripe& other) = default;
  Stripe(Stripe&& other) = default;
  Stripe& operator=(const Stripe& other) = delete;
  Stripe& operator=(Stripe&& other) = default;

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

  bool operator==(const Stripe& other) const {
    return
      prefix_       == other.prefix_ &&
      stripe_id_    == other.stripe_id_ &&
      width_        == other.width_ &&
      min_position_ == other.min_position_ &&
      max_position_ == other.max_position_ &&
      oids_         == other.oids_;
  }

  bool operator!=(const Stripe& other) const {
    return !this->operator==(other);
  }

 private:
  // index is the pre-computed value: position % stripe-width
  static std::string make_oid(const std::string& prefix,
      uint64_t stripe_id, uint32_t index);

  static std::vector<std::string> make_oids(const std::string& prefix,
    uint64_t stripe_id, uint32_t width);

  std::string prefix_;
  uint64_t stripe_id_;
  uint32_t width_;
  uint64_t min_position_;
  uint64_t max_position_;
  std::vector<std::string> oids_;
};

// MultiStripe is a compact representation of adjancent Stripe objects in the
// log position address space. Two adjacent Stripe objects can be represented by
// a single MultiStripe object if they are compatible---they have the same
// configuration (e.g. width and number of slots).
//
// Notes:
//   - it would seem that max position could always be derived from
//   min_position, instances, width, and slots. this is true if stripes are
//   allowed to always map their full range. i believe that in the future we may
//   want the ability to preemptively slice off an unused high-end range of a
//   stripe in order to deal with issues like fixing stripe configurations. so
//   instead we choose to explicitly specify the max position.
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
    assert(width_ > 0);
    assert(slots_ > 0);
    assert(instances_ > 0);

    // these restrictions aren't fundamental, but they happen to be true for the
    // current design.
    if (base_id_ > 0) {
      assert(min_position_ > 0);
    } else {
      assert(min_position_ == 0);
    }

    assert(min_position_ <= max_position_);

    // this relationship is true when we assume that the address space of a
    // stripe is always used / valid. that is, we don't cause part of a view
    // (e.g. the high end of the address range) to be remapped. this might not
    // hold in the future, but it does now for now.
    assert(max_position_ == (min_position_ + (instances_ * width_ * slots_) - 1));
  }

  MultiStripe(const MultiStripe& other) = default;
  MultiStripe(MultiStripe&& other) = default;
  MultiStripe& operator=(const MultiStripe& other) = delete;
  MultiStripe& operator=(MultiStripe&& other) = default;

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
    assert(min_position_ <= position);
    assert(position <= max_position_);
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

  bool operator==(const MultiStripe& other) const {
    return
      prefix_       == other.prefix_ &&
      base_id_      == other.base_id_ &&
      width_        == other.width_ &&
      slots_        == other.slots_ &&
      min_position_ == other.min_position_ &&
      instances_    == other.instances_ &&
      max_position_ == other.max_position_;
  }

  bool operator !=(const MultiStripe& other) const {
    return !this->operator==(other);
  }

 private:
  std::string prefix_;
  uint64_t base_id_;
  uint32_t width_;
  uint32_t slots_;
  uint64_t min_position_;
  uint64_t instances_;
  uint64_t max_position_;
};

}
