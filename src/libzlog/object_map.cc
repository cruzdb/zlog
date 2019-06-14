#include "object_map.h"
#include <set>
#include "libzlog/zlog.pb.h"
#include "include/zlog/options.h"

namespace zlog {

boost::optional<Stripe> ObjectMap::map_stripe(uint64_t position) const
{
  if (!stripes_by_pos_.empty()) {
    auto it = stripes_by_pos_.upper_bound(position);
    it = std::prev(it);
    assert(it->first <= position);
    if (position <= it->second.max_position()) {
      // position relative to the stripe
      const auto stripe_pos = position - it->first;
      // number of positions mapped by each stripe instance
      const auto stripe_size = it->second.width() * it->second.slots();
      // 0-based stripe instance mapping the position
      const auto stripe_instance = stripe_pos / stripe_size;
      // stripe id is the instance relative to the stripe base id
      const auto stripe_id = it->second.base_id() + stripe_instance;
      return stripe_by_id(stripe_id);
    }
  }
  return boost::none;
}

std::pair<boost::optional<std::string>, bool>
ObjectMap::map(const uint64_t position) const
{
  if (!stripes_by_pos_.empty()) {
    auto it = stripes_by_pos_.upper_bound(position);
    it = std::prev(it);
    assert(it->first <= position);
    if (position <= it->second.max_position()) {
      // position relative to the stripe
      const auto stripe_pos = position - it->first;
      // number of positions mapped by each stripe instance
      const auto stripe_size = it->second.width() * it->second.slots();
      // 0-based stripe instance mapping the position
      const auto stripe_instance = stripe_pos / stripe_size;
      // stripe id is the instance relative to the stripe base id
      const auto stripe_id = it->second.base_id() + stripe_instance;
      // generate the target object id
      auto oid = it->second.map(stripe_id, position);
      // the last stripe must also be the last instance
      auto last_stripe = std::next(it) == stripes_by_pos_.end() &&
        stripe_id == it->second.max_stripe_id();
      return std::make_pair(oid, last_stripe);
    }
  }
  return std::make_pair(boost::none, false);
}

boost::optional<std::vector<std::pair<std::string, bool>>>
ObjectMap::map_to(const uint64_t position) const
{
  // the max position is not mapped
  if (!map(position).first) {
    return boost::none;
  }

  // first: object name
  // second: complete map?
  std::vector<std::pair<std::string, bool>> objects;

  for (auto stripe_id = 0u; stripe_id < num_stripes(); stripe_id++) {
    const auto stripe = stripe_by_id(stripe_id);
    const auto oids = stripe.oids();

    const auto min_pos_base = stripe.min_position();

    // pos is below the minimum of this stripe. we're done
    if (min_pos_base > position) {
      break;
    }

    // this (likely) doesn't handle the future scenario where we chop off
    // stripes before they fill up.
    const auto max_pos_base = stripe.max_position() - (stripe.width() - 1);

    for (uint32_t i = 0; i < stripe.width(); i++) {
      const auto max_pos = max_pos_base + i;
      if (max_pos <= position) {
        objects.push_back(std::make_pair(oids[i], true));
        continue;
      }

      // pos may be the first/min position of the middle of the stripe
      const auto min_pos = min_pos_base + i;
      if (min_pos <= position) {
        objects.push_back(std::make_pair(oids[i], false));
        continue;
      }
    }
  }

  return objects;
}

void ObjectMap::expand_mapping(const std::string& prefix,
    const uint64_t position, const Options& options)
{
  assert(!map(position).first);

  do {
    const auto stripe_id = next_stripe_id_++;
    const auto it = stripes_by_pos_.rbegin();
    if (it != stripes_by_pos_.rend()) {
      it->second.extend();
      assert(it->second.max_stripe_id() == stripe_id);
    } else {
      const auto width = options.stripe_width;
      const auto slots = options.stripe_slots;
      const uint64_t max_position = width * slots - 1;
      auto res = stripes_by_pos_.emplace(0,
          MultiStripe{prefix, stripe_id, width, slots, 0, 1, max_position});
      assert(res.second);
      stripes_by_id_.emplace(stripe_id, res.first);
    }
  } while (!map(position).first);
}

boost::optional<ObjectMap> ObjectMap::expand_mapping(const std::string& prefix,
    const uint64_t position, const Options& options) const
{
  if (map(position).first) {
    return boost::none;
  }

  auto new_object_map = *this;
  new_object_map.expand_mapping(prefix, position, options);
  return new_object_map;
}

uint64_t ObjectMap::max_position() const
{
  auto stripe = stripes_by_pos_.crbegin();
  assert(stripe != stripes_by_pos_.crend());
  return stripe->second.max_position();
}

Stripe ObjectMap::stripe_by_id(uint64_t stripe_id) const
{
  assert(!stripes_by_id_.empty());
  auto it = stripes_by_id_.upper_bound(stripe_id);
  it = std::prev(it);
  assert(it->first <= stripe_id);
  assert(stripe_id <= it->second->second.max_stripe_id());
  return it->second->second.stripe_by_id(stripe_id);
}

ObjectMap ObjectMap::from_view(const std::string& prefix,
    const zlog_proto::View& view)
{
  std::map<uint64_t, MultiStripe> stripes;
  for (auto stripe : view.stripes()) {
    auto res = stripes.emplace(stripe.min_position(),
        MultiStripe(prefix, stripe.base_id(), stripe.width(), stripe.slots(),
          stripe.min_position(), stripe.instances(), stripe.max_position()));
    assert(res.second);
    (void)res;
  }

  if (!stripes.empty()) {
    std::set<uint64_t> ids;
    auto it = stripes.cbegin();
    auto it2 = std::next(it);
    for (; it != stripes.cend(); it++) {
      assert(it->first <= it->second.max_position());
      assert(it->second.width() > 0);
      // TODO assert ids with instance counts, too
      auto res = ids.emplace(it->second.base_id());
      assert(res.second);
      (void)res;
      if (it2 != stripes.cend()) {
        assert(it->second.max_position() < it2->first);
        it2++;
      }
    }
    assert(ids.find(view.next_stripe_id()) == ids.end());
  }

  return ObjectMap(view.next_stripe_id(), stripes);
}

}
