#include "sequencer.h"
#include <boost/optional.hpp>

namespace zlog {

boost::optional<SequencerConfig> SequencerConfig::decode(
      const zlog::fbs::Sequencer *seq)
{
  if (seq) {
    assert(seq->epoch() > 0);
    const auto token = flatbuffers::GetString(seq->token());
    assert(!token.empty());

    SequencerConfig conf(
        seq->epoch(),
        token,
        seq->position());

    return conf;
  }

  return boost::none;
}


flatbuffers::Offset<zlog::fbs::Sequencer> SequencerConfig::encode(
    flatbuffers::FlatBufferBuilder& fbb) const
{
  return zlog::fbs::CreateSequencerDirect(fbb,
      epoch_,
      token_.c_str(),
      position_);
}

nlohmann::json SequencerConfig::dump() const
{
  nlohmann::json j;
  j["epoch"] = epoch_;
  j["token"] = token_;
  j["position"] = position_;
  return j;
}

}
