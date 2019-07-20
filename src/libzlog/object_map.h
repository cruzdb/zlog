#pragma once
#include <map>
#include <boost/optional.hpp>
#include "stripe.h"
#include "libzlog/zlog_generated.h"
#include <nlohmann/json.hpp>

namespace zlog {

struct Options;

class ObjectMap {
 public:
  ObjectMap(uint64_t next_stripe_id,
      const std::map<uint64_t, MultiStripe>& stripes,
      uint64_t min_valid_position) :
    next_stripe_id_(next_stripe_id),
    stripes_by_pos_(stripes),
    min_valid_position_(min_valid_position)
  {
    // compute the stripes-by-id secondary index. if the set of stripes become
    // large enough that not using a secondary index is important, then it could
    // be restructured to store iterators into the primary index. when doing
    // this, make sure to recompute the iterators to avoid issues with copy/move
    // constructors.
    for (auto it = stripes_by_pos_.cbegin(); it != stripes_by_pos_.cend(); it++) {
      stripes_by_id_.emplace(it->second.base_id(), it->second);
    }

    assert(valid());
  }

  ObjectMap(const ObjectMap& other) = default;
  ObjectMap(ObjectMap&& other) = default;
  ObjectMap& operator=(const ObjectMap& other) = default;
  ObjectMap& operator=(ObjectMap&& other) = default;

 public:
  flatbuffers::Offset<zlog::fbs::ObjectMap> encode(
      flatbuffers::FlatBufferBuilder& fbb) const;

  static ObjectMap decode(const zlog::fbs::ObjectMap *object_map);

  nlohmann::json dump() const;

  bool valid() const;

 public:
  // returns the object name that maps the position, if it exists. the second
  // element is true iff the position maps to the last stripe in the object map.
  std::pair<boost::optional<std::string>, bool> map(uint64_t position) const;

  // expand the mapping to include the given position. true is returned when the
  // mapping changed, and false if the position is already mapped.
  boost::optional<ObjectMap> expand_mapping(uint64_t position,
      const Options& options) const;

  // returns a copy of this object map with a strictly larger
  // min_valid_position. otherwise boost::none is returned.
  boost::optional<ObjectMap> advance_min_valid_position(uint64_t position) const;

  // returns the stripe with the given stripe id.
  Stripe stripe_by_id(uint64_t stripe_id) const;

  // returns the id of the next stripe in the object map.
  uint64_t next_stripe_id() const {
    return next_stripe_id_;
  }

  // returns the maximum position mapped by the object map. do not call this
  // method if the object map is empty.
  uint64_t max_position() const;

  // returns the minimum (inclusive) valid log position
  uint64_t min_valid_position() const {
    return min_valid_position_;
  }

  // returns true if the object map contains no stripes.
  bool empty() const {
    return stripes_by_pos_.empty();
  }

  // returns the number of stripes.
  uint64_t num_stripes() const {
    return next_stripe_id_;
  }

  // iterate over objects that map from the beginning of the log up to the
  // position given. initialize stripe_id to 0, and done to false. when done
  // returns true, the return value can be ignored.
  boost::optional<std::vector<std::pair<std::string, bool>>> map_to(
      uint64_t position, uint64_t& stripe_id, bool& done) const;

  // return the stripe that maps the position.
  boost::optional<Stripe> map_stripe(uint64_t position) const;

  bool operator==(const ObjectMap& other) const {
    return
      next_stripe_id_ == other.next_stripe_id_ &&
      stripes_by_pos_ == other.stripes_by_pos_ &&
      stripes_by_id_ == other.stripes_by_id_ &&
      min_valid_position_ == other.min_valid_position_;
  }

 private:
  uint64_t next_stripe_id_;
  std::map<uint64_t, MultiStripe> stripes_by_pos_;
  std::map<uint64_t, MultiStripe> stripes_by_id_;
  uint64_t min_valid_position_;
};

}
