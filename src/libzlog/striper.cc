#include "striper.h"
#include "proto/zlog.pb.h"

// TODO:
//  - check for overflow when computing max pos
//  - collapse views instead of creating explicit copy of each
//  - handle view overlap so we can force seal a stripe
//  - fix naming scheme for objects

boost::optional<Striper::Mapping> Striper::MapPosition(uint64_t position) const
{
  std::lock_guard<std::mutex> l(lock_);

  assert(!views_.empty());
  auto it = views_.upper_bound(position);
  it--;

  assert(it->first <= position);
  if (position <= it->second.maxpos()) {
    auto oid = it->second.map(position);
    auto width = it->second.width();
    auto max_size = it->second.max_size();
    return Mapping{epoch_, width, max_size, oid};
  }

  return boost::none;
}

zlog_proto::View Striper::InitViewData(uint32_t width, uint32_t entries_per_object)
{
  assert(width > 0);
  assert(entries_per_object > 0);

  zlog_proto::View view;
  view.set_position(0);
  view.set_width(width);
  view.set_max_entry_size(1024); // TODO
  view.set_entries_per_object(entries_per_object);

  return view;
}

// the views_ data structure tries to collapse compatible views. as a result we
// can't reliably reproduce the latest view from this data structure, so we
// actually keep around a copy of the latest.
std::pair<uint64_t, zlog_proto::View> Striper::LatestView() const
{
  std::lock_guard<std::mutex> l(lock_);
  assert(!views_.empty());
  return std::make_pair(epoch_, latest_view_);
}

int Striper::Add(uint64_t epoch, const std::string& data)
{
  zlog_proto::View view;
  if (!view.ParseFromString(data)) {
    return -EIO;
  }

  assert(view.width() > 0);
  assert(view.entries_per_object() > 0);

  std::lock_guard<std::mutex> l(lock_);

  if (views_.empty()) {
    assert(epoch == 0);
    assert(view.position() == 0);
    uint64_t maxpos = (view.width() * view.entries_per_object()) - 1;
    epoch_ = 0;
    views_.emplace(0, ViewEntry(prefix_, epoch_, view.width(), maxpos,
          view.max_entry_size()));
  } else {
    assert(epoch == (epoch_ + 1));

    auto latest_view = views_.rbegin();
    assert(latest_view->first <= view.position());

    epoch_ = epoch;
    uint64_t maxpos = view.position() +
      (view.width() * view.entries_per_object()) - 1;
    views_.emplace(view.position(), ViewEntry(prefix_, epoch_, view.width(), maxpos,
          view.max_entry_size()));
  }

  latest_view_ = view;

  return 0;
}
