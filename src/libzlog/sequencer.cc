#include "sequencer.h"
#include <boost/optional.hpp>
#include "libzlog/zlog_generated.h"

namespace zlog {

boost::optional<SequencerConfig> SequencerConfig::from_view(
      const zlog::fbs::View *view)
{
  if (view->sequencer()) {
    const auto seq = view->sequencer();

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

}
