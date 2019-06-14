#include "sequencer.h"
#include <boost/optional.hpp>
#include "libzlog/zlog.pb.h"

namespace zlog {

boost::optional<SequencerConfig> SequencerConfig::from_view(
      const zlog_proto::View& view)
{
  if (view.has_seq()) {
    auto seq = view.seq();
    assert(seq.epoch() > 0);
    assert(!seq.secret().empty());
    SequencerConfig conf;
    conf.epoch = seq.epoch();
    conf.secret = seq.secret();
    conf.position = seq.position();
    return conf;
  }
  return boost::none;
}

}
