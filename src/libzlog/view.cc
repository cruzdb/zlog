#include "view.h"
#include <iostream>
#include "include/zlog/options.h"
#include "libzlog/zlog_generated.h"

namespace zlog {

View View::decode(const std::string& prefix,
    const std::string& view_data)
{
  flatbuffers::Verifier verifier(
      reinterpret_cast<const uint8_t*>(view_data.data()), view_data.size());
  if (!verifier.VerifyBuffer<zlog::fbs::View>(nullptr)) {
    assert(0);
    exit(1);
  }

  const auto view = flatbuffers::GetRoot<zlog::fbs::View>(
      reinterpret_cast<const uint8_t*>(view_data.data()));

  return View(
      ObjectMap::decode(prefix, view->object_map()),
      SequencerConfig::decode(view->sequencer()));
}

std::string View::create_initial(const Options& options)
{
  flatbuffers::FlatBufferBuilder fbb;

  // below the prefix is discarded when the object map is encoded
  // TODO: it would be nice to reformulate the abstractions to avoid needing to
  // use a placeholder prefix here. the multistripe defines a layout, but
  // shouldn't define a static object naming implied by requiring this prefix
  // parameter.
  std::map<uint64_t, MultiStripe> stripes;
  if (options.create_initial_view_stripes) {
    stripes.emplace(0,
        MultiStripe(
          "<<UNUSED PREFIX>>",
          0,
          options.stripe_width,
          options.stripe_slots,
          0,
          1,
          options.stripe_width * options.stripe_slots - 1));
  }

  const auto object_map = stripes.empty() ?
    zlog::fbs::CreateObjectMapDirect(fbb, 0, nullptr, 0) :
    ObjectMap(1, stripes, 0).encode(fbb);

  auto builder = zlog::fbs::ViewBuilder(fbb);
  builder.add_object_map(object_map);

  auto view = builder.Finish();
  fbb.Finish(view);

  return std::string(
      reinterpret_cast<const char*>(fbb.GetBufferPointer()), fbb.GetSize());
}

std::string View::encode() const
{
  flatbuffers::FlatBufferBuilder fbb;

  const auto encoded_object_map = object_map_.encode(fbb);

  flatbuffers::Offset<zlog::fbs::Sequencer> seq =
    seq_config_ ? seq_config_->encode(fbb) : 0;

  auto builder = zlog::fbs::ViewBuilder(fbb);
  builder.add_object_map(encoded_object_map);
  builder.add_sequencer(seq);

  auto view = builder.Finish();
  fbb.Finish(view);

  return std::string(
      reinterpret_cast<const char*>(fbb.GetBufferPointer()), fbb.GetSize());
}

boost::optional<View> View::expand_mapping(const std::string& prefix,
    const uint64_t position, const Options& options) const
{
  const auto new_object_map = object_map_.expand_mapping(prefix, position,
      options);
  if (new_object_map) {
    return View(*new_object_map, seq_config_);
  }
  return boost::none;
}


boost::optional<View> View::advance_min_valid_position(uint64_t position) const
{
  const auto new_object_map = object_map_.advance_min_valid_position(position);
  if (new_object_map) {
    return View(*new_object_map, seq_config_);
  }
  return boost::none;
}

View View::set_sequencer_config(SequencerConfig seq_config) const
{
  return View(object_map_, seq_config);
}

}
