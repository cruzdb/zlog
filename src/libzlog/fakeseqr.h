#pragma once
#include <deque>
#include <iostream>
#include "libzlog/log_impl.h"

// fake sequencer is designed to manage sequence for many different logs. but it
// is only used in practice to manage a single log. thus, the past
// differentiator, the pool name, is fixed. we should simply the design...
class FakeSeqrClient : public zlog::SeqrClient {
 public:
  // TODO: wow this api sucks
  FakeSeqrClient(const std::map<std::string, std::string>& meta,
      const std::string& name, uint64_t init_position, uint64_t epoch) :
    SeqrClient("", "", epoch),
    pool("0xdeadbeef")
  {
    entry *e = &entries_[std::make_pair(pool, name)];
    e->seq = init_position;
  }

  void Connect() {}

  virtual int CheckTail(uint64_t epoch,
      const std::map<std::string, std::string>& meta,
      const std::string& name, uint64_t *position, bool next)
  {
    entry *e;
    auto it = entries_.find(std::make_pair(pool, name));
    if (it == entries_.end()) {
      // TODO
      assert(0);
      e = &entries_[std::make_pair(pool, name)];
      e->seq = 0;
    } else
      e = &it->second;
    
    if (next) {
      uint64_t tail = e->seq.fetch_add(1); // returns previous value
      *position = tail;
    } else
      *position = e->seq.load();

    return 0;
  }

  virtual int CheckTail(uint64_t epoch,
      const std::map<std::string, std::string>& meta,
      const std::string& name, std::vector<uint64_t>& positions, size_t count)
  {
    assert(0);
    exit(1);
    return -EOPNOTSUPP;
  }

 private:
  const std::string pool;

  struct entry {
    std::atomic<uint64_t> seq;
  };

  std::map<std::pair<std::string, std::string>, entry> entries_;
};
