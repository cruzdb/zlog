#pragma once
#include <memory>
#include <string>
#include <boost/optional.hpp>
#include "object_map.h"
#include "sequencer.h"

namespace zlog {
  namespace fbs {
    class View;
  }
}

namespace zlog {

struct Options;

class View {
 public:
  View(ObjectMap object_map, boost::optional<SequencerConfig> seq_config) :
    object_map_(object_map),
    seq_config_(seq_config)
  {}

  View(const View& other) = delete;
  View(View&& other) = default;
  View& operator=(const View& other) = delete;
  View& operator=(View&& other) = delete;

 public:
  // deserialize view
  static View decode(const std::string& prefix,
      const std::string& view_data);

  // create a view serialization suitable as an initial view
  static std::string create_initial(const Options& options);

  // serialize this view instance
  std::string encode() const;

 public:
  // returns a copy of this view that maps the given position. if the position
  // is already mapped then boost::none is returned.
  virtual boost::optional<View> expand_mapping(const std::string& prefix,
      uint64_t position, const Options& options) const;

  // returns a copy of this view with a strictly larger min_valid_position.
  // otherwise boost::none is returned.
  virtual boost::optional<View> advance_min_valid_position(
      uint64_t position) const;

  View set_sequencer_config(SequencerConfig seq_config) const;

  const ObjectMap& object_map() const {
    return object_map_;
  }

  const boost::optional<SequencerConfig>& seq_config() const {
    return seq_config_;
  }

 private:
  ObjectMap object_map_;
  boost::optional<SequencerConfig> seq_config_;
};

// can make const?
class VersionedView : public View {
 public:
  VersionedView(const std::string& prefix, const uint64_t epoch,
      const std::string& view_data) :
    View(View::decode(prefix, view_data)),
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
