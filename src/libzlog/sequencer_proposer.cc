#include "libzlog/sequencer_proposer.h"

#include "libzlog/log_backend.h"
#include "libzlog/stripe.h"
#include "libzlog/view.h"
#include "libzlog/view_reader.h"

namespace zlog {

SequencerProposer::SequencerProposer(LogBackend *backend,
    ViewReader *view_reader) :
  backend_(backend),
  view_reader_(view_reader)
{
  assert(backend_);
  assert(view_reader_);
  assert(view_reader_->view());
}

int SequencerProposer::propose()
{
  int retries = 5;
  std::chrono::milliseconds delay(125);

  while (true) {
    // read the current view
    const auto curr_view = view_reader_->view();
    const auto next_epoch = curr_view->epoch() + 1;

    // find the maximum position written to use as a seed for the sequencer. the
    // maximum position written is contained in the first non-empty stripe
    // scanning in reverse, beginning with the stripe that maps the maximum
    // possible position for the current view.

    // empty: if the log is empty
    // max_pos: defined iff empty is false
    bool empty = true;
    uint64_t max_pos;

    if (!curr_view->object_map().empty()) {
      assert(curr_view->object_map().num_stripes() > 0);
      for (auto stripe_id = curr_view->object_map().num_stripes(); stripe_id--;) {
        const auto stripe = curr_view->object_map().stripe_by_id(stripe_id);
        int ret = seal_stripe(stripe, next_epoch, &max_pos, &empty);
        if (ret < 0) {
          return ret;
        }
        if (!empty) {
          break;
        }
      }
    }

    // XXX stop sealing after we find the max position to use as the sequencer
    // seed. continuing to seal more stripes (perhaps asynchronously) may provide
    // some benefit to signaling other clients to refresh their view, but should
    // not affect correctness; in affect, we can tolerate multiple sequencers.

    // see the view reader for more info on sequencer config
    const SequencerConfig seq_config(next_epoch, backend_->token(),
        (empty ? uint64_t(0) : (max_pos + 1)));

    // build the new view that'll be proposed
    const auto new_view = curr_view->with_sequencer_config(seq_config);

    // propose the next view
    const auto data = new_view.encode();
    int ret = backend_->ProposeView(next_epoch, data);

    // successful proposal. the caller still needs to examine the latest view to
    // determine if the sequencer proposed is active--another proposal could have
    // happened immediately after this one.
    if (!ret) {
      view_reader_->wait_for_newer_view(curr_view->epoch(), true);
      return 0;
    }

    // another view was successfully proposed. w.r.t. the latest view:
    //
    //   1. if it has no sequencer config, then retry.
    //   2. if it has a sequencer config and it's unchanged from when we began
    //      the proposal process, then retry. could be a new view for an
    //      expanded mapping.
    //   3. otherwise another sequencer proposal was successful
    //
    //   Note that these are heuristics to avoid some common races, and don't
    //   affect correctness.
    //
    if (ret == -ESPIPE) {
      view_reader_->wait_for_newer_view(curr_view->epoch(), true);
      const auto updated_view = view_reader_->view();
      if (!updated_view->seq_config() ||
          updated_view->seq_config() == curr_view->seq_config()) {
        if (--retries == 0) {
          return -ETIMEDOUT;
        }
        std::this_thread::sleep_for(delay);
        delay *= 2;
        continue;
      }
      return -EINTR;
    }

    return ret;
  }
}

int SequencerProposer::seal_stripe(const Stripe& stripe, uint64_t epoch,
    uint64_t *pposition, bool *pempty) const
{
  auto& oids = stripe.oids();
  assert(!oids.empty());

  // Out-of-date epoch (-ESPIPE) is ignored. Sealing these objects ensures that
  // their stored epochs are set _at least_ to the sealing epoch. Any operations
  // we compute on the objects after sealing (e.g. MaxPos) don't take affect
  // unless we are later able to successfully propose the sealing epoch.
  // Allowing this helps scenarios like sealing a stripe that was partially
  // sealed and then the new sealing task encountering an older epoch stored
  // than what is available as the latest view. This is effectively OCC.
  for (auto& oid : oids) {
    int ret = backend_->Seal(oid, epoch);
    if (ret < 0 && ret != -ESPIPE) {
      return ret;
    }
  }

  bool stripe_empty = true;
  // max pos only defined for non-empty stripe
  uint64_t stripe_max_pos = 0;

  for (auto& oid : oids) {
    bool empty;
    uint64_t max_pos;
    int ret = backend_->MaxPos(oid, &max_pos, &empty);
    if (ret < 0) {
      return ret;
    }

    if (empty) {
      continue;
    }

    stripe_empty = false;
    stripe_max_pos = std::max(stripe_max_pos, max_pos);
  }

  if (pempty) {
    *pempty = stripe_empty;
  }

  if (pposition) {
    if (!stripe_empty) {
      *pposition = stripe_max_pos;
    }
  }

  return 0;
}

}
