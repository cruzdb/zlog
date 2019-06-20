#include "sequencer.h"
#include <boost/optional.hpp>

namespace zlog {

boost::optional<SequencerConfig> SequencerConfig::decode(
      const zlog::fbs::Sequencer *seq)
{
  if (seq) {
    assert(seq->epoch() > 0);
    const auto secret = flatbuffers::GetString(seq->secret());
    assert(!secret.empty());

    SequencerConfig conf;
    conf.epoch = seq->epoch();
    conf.secret = secret;
    conf.position = seq->position();

    return conf;
  }

  return boost::none;
}


flatbuffers::Offset<zlog::fbs::Sequencer> SequencerConfig::encode(
    flatbuffers::FlatBufferBuilder& fbb) const
{
  return zlog::fbs::CreateSequencerDirect(fbb,
      epoch,
      secret.c_str(),
      position);
}

}
