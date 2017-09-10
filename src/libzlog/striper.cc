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

std::string Striper::BuildViewData(uint64_t pos,
    uint32_t width)
{
  zlog_proto::View view;
  view.set_position(pos);
  view.set_width(width);

  std::string result;
  assert(view.SerializeToString(&result));
  return result;
}

std::string Striper::NewViewData(uint64_t pos) const
{
  std::lock_guard<std::mutex> l(lock_);
  assert(!views_.empty());
  auto width = views_.rbegin()->second;
  return BuildViewData(pos, width);
}

std::string Striper::NewResumeViewData() const
{
  std::lock_guard<std::mutex> l(lock_);
  assert(!views_.empty());
  auto pos = views_.rbegin()->first;
  auto width = views_.rbegin()->second;
  return BuildViewData(pos, width);
}

std::string Striper::InitViewData(uint32_t width)
{
  return BuildViewData(0, width);
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
