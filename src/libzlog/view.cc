#include "view.h"
#include <iostream>
#include "include/zlog/options.h"
#include "libzlog/zlog.pb.h"

namespace zlog {

std::string View::create_initial(const Options& options)
{
  std::string blob;
  zlog_proto::View view;
  view.set_min_valid_position(0);
  if (options.create_initial_view_stripes) {
    // TODO: implement
  }
  if (!view.SerializeToString(&blob)) {
    assert(0);
    exit(1);
  }
  return blob;
}

std::string View::serialize() const
{
  zlog_proto::View view;

  // TODO: good reason for object_map serializing itself
  for (const auto& stripe : object_map.multi_stripes()) {
    auto pb_stripe = view.add_stripes();
    pb_stripe->set_base_id(stripe.second.base_id());
    pb_stripe->set_width(stripe.second.width());
    pb_stripe->set_slots(stripe.second.slots());
    pb_stripe->set_instances(stripe.second.instances());
    pb_stripe->set_min_position(stripe.first);
    pb_stripe->set_max_position(stripe.second.max_position());
  }
  view.set_next_stripe_id(object_map.next_stripe_id());

  if (seq_config) {
    auto seq = view.mutable_seq();
    seq->set_epoch(seq_config->epoch);
    seq->set_secret(seq_config->secret);
    seq->set_position(seq_config->position);
  }

  view.set_min_valid_position(min_valid_position);

  std::string blob;
  if (!view.SerializeToString(&blob)) {
    std::cerr << "invalid proto" << std::endl << std::flush;
    assert(0);
    exit(1);
    return "";
  }

  return blob;
}

View::View(const std::string& prefix, const zlog_proto::View& view) :
  object_map(ObjectMap::from_view(prefix, view)),
  min_valid_position(view.min_valid_position()),
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
