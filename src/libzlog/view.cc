#include "view.h"
#include <iostream>
#include "include/zlog/options.h"
#include "libzlog/zlog_generated.h"

namespace zlog {

std::string View::create_initial(const Options& options)
{
  flatbuffers::FlatBufferBuilder fbb;
  auto builder = zlog::fbs::ViewBuilder(fbb);

  builder.add_next_stripe_id(0);
  builder.add_min_valid_position(0);
  if (options.create_initial_view_stripes) {
    // TODO: implement
  }

  auto view = builder.Finish();
  fbb.Finish(view);

  return std::string(
      reinterpret_cast<const char*>(fbb.GetBufferPointer()), fbb.GetSize());
}

std::string View::serialize() const
{
  flatbuffers::FlatBufferBuilder fbb;

  // serialize the multi-stripes
  std::vector<flatbuffers::Offset<zlog::fbs::MultiStripe>> stripes;
  for (const auto& stripe : object_map.multi_stripes()) {
    auto s = zlog::fbs::CreateMultiStripe(fbb,
        stripe.second.base_id(),
        stripe.second.width(),
        stripe.second.slots(),
        stripe.second.instances(),
        stripe.first,
        stripe.second.max_position());
    stripes.push_back(s);
  }

  // serialize sequencer config
  flatbuffers::Offset<zlog::fbs::Sequencer> sequencer_config = 0;
  if (seq_config) {
    sequencer_config = zlog::fbs::CreateSequencerDirect(fbb,
        seq_config->epoch,
        seq_config->secret.c_str(),
        seq_config->position);
  }

  auto view = zlog::fbs::CreateViewDirect(fbb,
      object_map.next_stripe_id(),
      &stripes,
      sequencer_config,
      min_valid_position);
  fbb.Finish(view);

  return std::string(
      reinterpret_cast<const char*>(fbb.GetBufferPointer()), fbb.GetSize());
}

View::View(const std::string& prefix, const zlog::fbs::View *view) :
  object_map(ObjectMap::from_view(prefix, view)),
  min_valid_position(view->min_valid_position()),
  seq_config(SequencerConfig::from_view(view))
{}

boost::optional<View> View::expand_mapping(const std::string& prefix,
    const uint64_t position, const Options& options) const
{
  const auto new_object_map = object_map.expand_mapping(prefix, position,
      options);
  if (new_object_map) {
    return View(*new_object_map, min_valid_position, seq_config);
  }
  return boost::none;
}


boost::optional<View> View::advance_min_valid_position(uint64_t position) const
{
  if (position <= min_valid_position) {
    return boost::none;
  }
  return View(object_map, position, seq_config);
}

View View::set_sequencer_config(SequencerConfig seq_config) const
{
  return View(object_map, min_valid_position, seq_config);
}

}
