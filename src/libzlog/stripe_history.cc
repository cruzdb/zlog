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
  uint64_t latest_pos;
  Stripe latest = LatestStripe(&latest_pos);
  latest.epoch = epoch;

  /*
   * This should probably be handled later in Seal after we make Seal aware of
   * cls_zlog v2. But basically what is happening here is that a stripe was
   * previously sealed. The history might look like [0, 11, 21, +inf) where
   * position 21 is mapped to the latest stripe. But when we seal and clone
   * the latest no writes actually occurred to the stripe so we get back
   * max_pos of 0.
   *
   * The basic solution we are using here is to create a new stripe starting
   * at the next position. The new history is [0, 11, 21, 22, +inf) so that
   * new stripe is left with only 21 mapping into it.
   *
   * FIXME: ideally I think we should use a data structure that lets us
   * explicitly represent what happened. That is allow duplicate positions in
   * the map. So each position would be a list with the last element being the
   * active stripe and the others being empty.
   */
  if (position == 0)
    position = latest_pos + 1;

  const auto it = history_.lower_bound(position);
  assert(it == history_.end());

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

StripeHistory::Stripe StripeHistory::LatestStripe(uint64_t *pos) const
{
  const auto it = history_.rbegin();
  assert(it != history_.rend());
  if (pos)
    *pos = it->first;
  return it->second;
}
