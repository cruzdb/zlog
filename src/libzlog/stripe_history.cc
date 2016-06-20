#include "stripe_history.h"
#include "proto/zlog.pb.h"
#include "proto/protobuf_bufferlist_adapter.h"

ceph::bufferlist StripeHistory::Serialize() const
{
  zlog_proto::MetaLog config;

  for (const auto& stripe : history_) {
    uint64_t position = stripe.first;
    const Stripe& s = stripe.second;

    zlog_proto::MetaLog_StripeHistoryEntry *entry;
    entry = config.add_stripe_history();
    entry->set_pos(position);
    entry->set_epoch(s.epoch);
    entry->set_width(s.width);
  }

  ceph::bufferlist bl;
  pack_msg<zlog_proto::MetaLog>(bl, config);

  return bl;
}

int StripeHistory::Deserialize(ceph::bufferlist& bl)
{
  zlog_proto::MetaLog config;
  if (!unpack_msg<zlog_proto::MetaLog>(config, bl)) {
    std::cerr << "failed to parse configuration" << std::endl;
    return -EIO;
  }

  for (unsigned i = 0; i < config.stripe_history_size(); i++) {
    const zlog_proto::MetaLog_StripeHistoryEntry& e = config.stripe_history(i);
    uint64_t position = e.pos();
    assert(history_.find(position) == history_.end());
    Stripe stripe = { e.epoch(), (int)e.width() };
    history_[position] = stripe;
  }

  return 0;
}

bool StripeHistory::Empty() const {
  return history_.empty();
}

void StripeHistory::AddStripe(uint64_t position, uint64_t epoch, int width)
{
  const auto it = history_.lower_bound(position);
  assert(it == history_.end());
  assert(width > 0);
  Stripe stripe = { epoch, width };
  history_[position] = stripe;
}

void StripeHistory::CloneLatestStripe(uint64_t position, uint64_t epoch)
{
  const auto it = history_.lower_bound(position);
  assert(it == history_.end());

  Stripe latest = LatestStripe();
  latest.epoch = epoch;

  history_[position] = latest;
}

StripeHistory::Stripe StripeHistory::FindStripe(uint64_t position) const
{
  assert(!history_.empty());
  auto it = history_.upper_bound(position);
  assert(it != history_.begin());
  it--;
  return it->second;
}

StripeHistory::Stripe StripeHistory::LatestStripe() const
{
  const auto it = history_.rbegin();
  assert(it != history_.rend());
  return it->second;
}
