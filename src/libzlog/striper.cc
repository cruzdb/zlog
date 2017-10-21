#include "striper.h"
#include <sstream>
#include "proto/zlog.pb.h"

Striper::Mapping Striper::MapPosition(uint64_t position) const
{
  std::lock_guard<std::mutex> l(lock_);
  assert(!views_.empty());
  auto it = views_.upper_bound(position);
  it--;

  auto width = it->second;
  auto oid = oids_[position % width];

  return Mapping{epoch_, oid};
}

zlog_proto::View Striper::InitViewData(uint32_t width)
{
  assert(width > 0);
  zlog_proto::View view;
  view.set_position(0);
  view.set_width(width);
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

  std::lock_guard<std::mutex> l(lock_);

  if (views_.empty()) {
    assert(epoch == 0);
    assert(view.position() == 0);
    views_.emplace(0, view.width());
    epoch_ = 0;
    GenerateObjects();
  } else {
    assert(epoch == (epoch_ + 1));
    assert(views_.rbegin()->first <= view.position());
    if (views_.rbegin()->second != view.width()) {
      auto res = views_.emplace(view.position(), view.width());
      assert(res.second);
      GenerateObjects();
    }
    epoch_ = epoch;
  }

  latest_view_ = view;

  return 0;
}

void Striper::GenerateObjects()
{
  assert(!views_.empty());

  auto it = views_.rbegin();
  auto position = it->first;
  auto width = it->second;

  std::vector<std::string> oids;
  for (uint32_t i = 0; i < width; i++) {
    std::stringstream oid;
    oid << prefix_ << "." << position << "." << i;
    oids.push_back(oid.str());
  }

  oids_.swap(oids);
}
