#include "stripe_history.h"
#include "zlog.pb.h"
#include "protobuf_bufferlist_adapter.h"

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
    history_[position] = e.width();
  }

  return 0;
}

bool StripeHistory::Empty() const {
  return history_.empty();
}

void StripeHistory::AddStripe(uint64_t position, int width)
{
  const auto it = history_.lower_bound(position);
  assert(it == history_.end());
  assert(width > 0);
  history_[position] = width;
}

int StripeHistory::FindStripeSize(uint64_t position) const
{
  assert(!history_.empty());
  auto it = history_.upper_bound(position);
  assert(it != history_.begin());
  it--;
  return it->second;
}

int StripeHistory::LatestStripe() const
{
  const auto it = history_.rbegin();
  assert(it != history_.rend());
  return it->second;
}

ceph::bufferlist StripeHistory::Serialize() const
{
  zlog_proto::MetaLog config;

  for (const auto& stripe : history_) {
    zlog_proto::MetaLog_StripeHistoryEntry *entry;
    entry = config.add_stripe_history();
    entry->set_pos(stripe.first);
    entry->set_width(stripe.second);
  }

  ceph::bufferlist bl;
  pack_msg<zlog_proto::MetaLog>(bl, config);

  return bl;
}
