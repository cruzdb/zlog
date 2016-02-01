#include "log_mapper.h"
#include <sstream>
#include "stripe_history.h"

std::string LogMapper::SlotToOid(int slot) const
{
    std::stringstream oid;
    oid << log_name_ << "." << slot;
    return oid.str();
}

void LogMapper::LatestObjectSet(std::vector<std::string>& objects,
    const StripeHistory& history) const
{
  int stripe_size = history.LatestStripe();
  std::vector<std::string> result;
  for (int slot = 0; slot < stripe_size; slot++) {
    result.push_back(SlotToOid(slot));
  }
  objects.swap(result);
}

std::string LogMapper::FindObject(uint64_t position) const
{
  assert(!history_.Empty());
  int stripe_size = history_.FindStripeSize(position);
  int slot = position % stripe_size;
  return SlotToOid(slot);
}
