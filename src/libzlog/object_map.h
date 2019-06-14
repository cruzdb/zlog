#pragma once
#include <map>
#include <boost/optional.hpp>
#include "stripe.h"

namespace zlog_proto {
  class View;
}

namespace zlog {

struct Options;

class ObjectMap {
 public:
  static ObjectMap from_view(const std::string& prefix,
      const zlog_proto::View& view);

 public:
  // returns the object name that maps the position, if it exists. the second
  // element is true iff the position maps to the last stripe in the object map.
  std::pair<boost::optional<std::string>, bool> map(uint64_t position) const;

  // expand the mapping to include the given position. true is returned when the
  // mapping changed, and false if the position is already mapped.
  boost::optional<ObjectMap> expand_mapping(const std::string& prefix,
      uint64_t position, const Options& options) const;

  // returns the stripe with the given stripe id.
  Stripe stripe_by_id(uint64_t stripe_id) const;

  // returns the id of the next stripe in the object map.
  uint64_t next_stripe_id() const {
    return next_stripe_id_;
  }

  // returns the maximum position mapped by the object map.
  uint64_t max_position() const;

  // returns true if the object map contains no stripes.
  bool empty() const {
    return stripes_by_pos_.empty();
  }

  // returns the number of stripes.
  uint64_t num_stripes() const {
    return next_stripe_id_;
  }

  const std::map<uint64_t, MultiStripe>& multi_stripes() const {
    return stripes_by_pos_;
  }

  boost::optional<std::vector<std::pair<std::string, bool>>> map_to(
      uint64_t position) const;

  // return the stripe that maps the position.
  boost::optional<Stripe> map_stripe(uint64_t position) const;

 private:
  ObjectMap(uint64_t next_stripe_id,
      const std::map<uint64_t, MultiStripe>& stripes) :
    next_stripe_id_(next_stripe_id),
    stripes_by_pos_(stripes)
  {
    for (auto it = stripes_by_pos_.cbegin(); it != stripes_by_pos_.cend(); it++) {
      stripes_by_id_.emplace(it->second.base_id(), it);
    }
  }

  void expand_mapping(const std::string& prefix, uint64_t position,
      const Options& options);

  uint64_t next_stripe_id_;
  std::map<uint64_t, MultiStripe> stripes_by_pos_;
  std::map<uint64_t, std::map<uint64_t, MultiStripe>::const_iterator> stripes_by_id_;
};

}
