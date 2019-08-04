#pragma once
#include <memory>

namespace zlog {

class LogBackend;
class ViewReader;
class Stripe;

class SequencerProposer final {
 public:
  SequencerProposer(LogBackend *backend, ViewReader *view_reader);

  SequencerProposer(const SequencerProposer& other) = delete;
  SequencerProposer(SequencerProposer&& other) = delete;
  SequencerProposer& operator=(const SequencerProposer& other) = delete;
  SequencerProposer& operator=(SequencerProposer&& other) = delete;

 public:
  // propose a view with a new sequencer. when success (0) is returned the
  // proposal was successful, but the caller should still verify that the
  // sequencer is configured as expected.
  int propose();

 private:
  // seals the given stripe with the given epoch. on success, *pempty will be
  // set to true if the stripe is empty (no positions have been written, filled,
  // etc...). if the stripe is non-empty, *pposition will be set to the maximum
  // position written. otherwise it is left unmodified.
  int seal_stripe(const Stripe& stripe, uint64_t epoch,
      uint64_t *pposition, bool *pempty) const;

 private:
  LogBackend *backend_;
  ViewReader *view_reader_;
};

}
