#pragma once
#include <deque>
#include <iostream>
#include "libzlog/log_impl.h"

// fake sequencer is designed to manage sequence for many different logs. but it
// is only used in practice to manage a single log. thus, the past
// differentiator, the pool name, is fixed. we should simply the design...
class FakeSeqrClient : public zlog::SeqrClient {
 public:
  FakeSeqrClient(const std::map<std::string, std::string>& meta,
      const std::string& name, bool empty, uint64_t position,
      uint64_t epoch) : SeqrClient("", "", epoch), pool("0xdeadbeef")
  {
    entry *e = &entries_[std::make_pair(pool, name)];
    if (empty)
      e->seq = 0;
    else
      e->seq = position + 1;
  }

  void Connect() {}

  virtual int CheckTail(uint64_t epoch,
      const std::map<std::string, std::string>& meta,
      const std::string& name, uint64_t *position, bool next)
  {
    entry *e;
    auto it = entries_.find(std::make_pair(pool, name));
    if (it == entries_.end()) {
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

  virtual int CheckTail(uint64_t epoch,
      const std::map<std::string, std::string>& meta,
      const std::string& name, const std::set<uint64_t>& stream_ids,
      std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
      uint64_t *position, bool next)
  {
    if (stream_ids.size() == 0)
      return -EINVAL;

    entry *e;
    auto it = entries_.find(std::make_pair(pool, name));
    if (it == entries_.end()) {
      e = &entries_[std::make_pair(pool, name)];
      e->seq = 0;
    } else
      e = &it->second;

    if (next) {
      std::map<uint64_t, std::vector<uint64_t>> result;

      // make a copy of the current backpointers
      for (std::set<uint64_t>::const_iterator it = stream_ids.begin();
          it != stream_ids.end(); it++) {

        uint64_t stream_id = *it;
        stream_index_t::const_iterator stream_it = e->streams.find(stream_id);
        if (stream_it == e->streams.end()) {
          /*
           * If a stream doesn't exist initialize an empty set of backpointers.
           * How do we know a stream doesn't exist? During log initialization we
           * setup all existing logs...
           */
          e->streams[stream_id] = stream_backpointers_t();

          std::vector<uint64_t> ptrs;
          result[stream_id] = ptrs;
          continue;
        }

        std::vector<uint64_t> ptrs(stream_it->second.begin(),
            stream_it->second.end());
        result[stream_id] = ptrs;
      }

      uint64_t next_pos = e->seq.fetch_add(1);

      // add new position to each stream
      for (std::set<uint64_t>::const_iterator it = stream_ids.begin();
          it != stream_ids.end(); it++) {
        uint64_t stream_id = *it;
        stream_backpointers_t& backpointers = e->streams.at(stream_id);
        backpointers.push_back(next_pos);
        if (backpointers.size() > 10)
          backpointers.pop_front();
      }

      if (position)
        *position = next_pos;
      stream_backpointers.swap(result);

      return 0;
    } else {
      std::map<uint64_t, std::vector<uint64_t>> result;

      // make a copy of the current backpointers
      for (std::set<uint64_t>::const_iterator it = stream_ids.begin();
          it != stream_ids.end(); it++) {

        uint64_t stream_id = *it;
        stream_index_t::const_iterator stream_it = e->streams.find(stream_id);
        if (stream_it == e->streams.end()) {
          /*
           * If a stream doesn't exist initialize an empty set of backpointers.
           * How do we know a stream doesn't exist? During log initialization we
           * setup all existing logs...
           */
          e->streams[stream_id] = stream_backpointers_t();

          std::vector<uint64_t> ptrs;
          result[stream_id] = ptrs;
          continue;
        }

        std::vector<uint64_t> ptrs(stream_it->second.begin(),
            stream_it->second.end());
        result[stream_id] = ptrs;
      }

      if (position)
        *position = e->seq.load();
      stream_backpointers.swap(result);

      return 0;
    }
  }

 private:
  typedef std::deque<uint64_t> stream_backpointers_t;
  typedef std::map<uint64_t, stream_backpointers_t> stream_index_t;

  const std::string pool;

  struct entry {
    std::atomic<uint64_t> seq;
    stream_index_t streams;
  };

  std::map<std::pair<std::string, std::string>, entry> entries_;
};
