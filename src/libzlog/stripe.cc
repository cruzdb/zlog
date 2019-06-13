#include "stripe.h"
#include <sstream>

namespace zlog {

std::string Stripe::make_oid(const std::string& prefix,
    uint64_t stripe_id, uint32_t index)
{
  std::stringstream oid;
  oid << prefix << "." << stripe_id << "." << index;
  return oid.str();
}

std::string Stripe::make_oid(const std::string& prefix,
    uint64_t stripe_id, uint32_t width, uint64_t position)
{
  auto index = position % width;
  return make_oid(prefix, stripe_id, index);
}

std::vector<std::string> Stripe::make_oids()
{
  std::vector<std::string> oids;
  oids.reserve(width_);

  for (uint32_t i = 0; i < width_; i++) {
    oids.emplace_back(make_oid(prefix_, stripe_id_, i));
  }

  return oids;
}

}
