#include "log_mapper.h"
#include <mutex>
#include <sstream>
#include "stripe_history.h"

std::string LogMapper::SlotToOid(uint64_t epoch, int slot) const
{
    std::stringstream oid;
    oid << log_name_ << "." << epoch << "." << slot;
    return oid.str();
}

uint64_t LogMapper::Epoch() {
  return epoch_;
}

void LogMapper::SetHistory(const StripeHistory& history, uint64_t epoch) {
  std::lock_guard<std::mutex> l(lock_);
  assert(!history.Empty());
  history_ = history;
  epoch_ = epoch;
}

void LogMapper::LatestObjectSet(std::vector<std::string>& objects,
    const StripeHistory& history)
{
  std::lock_guard<std::mutex> l(lock_);
  const StripeHistory::Stripe stripe = history.LatestStripe();
  std::vector<std::string> result;
  for (int slot = 0; slot < stripe.width; slot++) {
    result.push_back(SlotToOid(stripe.epoch, slot));
  }
  objects.swap(result);
}

void LogMapper::FindObject(uint64_t position, std::string *oid, uint64_t *epoch)
{
  std::lock_guard<std::mutex> l(lock_);
  assert(!history_.Empty());
  const StripeHistory::Stripe stripe = history_.FindStripe(position);
  int slot = position % stripe.width;
  *oid = SlotToOid(stripe.epoch, slot);
  if (epoch)
    *epoch = epoch_;
}

int LogMapper::CurrentStripeWidth()
{
  std::lock_guard<std::mutex> l(lock_);
  assert(!history_.Empty());
  const StripeHistory::Stripe stripe = history_.LatestStripe();
  return stripe.width;
}
