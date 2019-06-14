#pragma once
#include <memory>
#include <string>
#include <boost/optional.hpp>
#include "object_map.h"
#include "sequencer.h"

namespace zlog_proto {
  class View;
}

namespace zlog {

struct Options;

class View {
 public:
  View(const std::string& prefix, const zlog_proto::View& view);

  // returns a copy of this view that maps the given position. if the position
  // is already mapped then boost::none is returned.
  virtual boost::optional<View> expand_mapping(const std::string& prefix,
      uint64_t position, const Options& options) const;

  // returns a copy of this view with a strictly larger min_valid_position.
  // otherwise boost::none is returned.
  virtual boost::optional<View> advance_min_valid_position(
      uint64_t position) const;

  View set_sequencer_config(SequencerConfig seq_config) const;

  static std::string create_initial(const Options& options);

  std::string serialize() const;

  const ObjectMap object_map;
  const uint64_t min_valid_position;
  const boost::optional<SequencerConfig> seq_config;

 private:
  View(const ObjectMap object_map, const uint64_t min_valid_position,
      const boost::optional<SequencerConfig> seq_config) :
    object_map(object_map),
    min_valid_position(min_valid_position),
    seq_config(seq_config)
  {}
};

class VersionedView : public View {
 public:
  VersionedView(const std::string& prefix, const uint64_t epoch,
      const zlog_proto::View& view) :
    View(prefix, view),
    epoch_(epoch)
  {}

  uint64_t epoch() const {
    return epoch_;
  }

  std::shared_ptr<Sequencer> seq;

 private:
  const uint64_t epoch_;
};

}
