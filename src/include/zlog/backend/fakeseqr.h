#ifndef ZLOG_INCLUDE_ZLOG_FAKESEQR_H
#define ZLOG_INCLUDE_ZLOG_FAKESEQR_H
#include <deque>
#include "libzlog/log_impl.h"

class FakeSeqrClient : public zlog::SeqrClient {
 public:
  FakeSeqrClient() : SeqrClient("", "")
  {}

  void Connect() {}

  /*
   * The networked sequencer opens a target log to initialize its state. The
   * fake sequencer can initialize its state from a log instance, otherwise it
   * will initialize its state assuming the log is empty.
   *
   * doesn't handle stream interface...
   */
  void Init(zlog::Log *baselog, std::string pool, std::string name) {
    uint64_t epoch;
    uint64_t position;
    zlog::LogImpl *log = reinterpret_cast<zlog::LogImpl*>(baselog);
    int ret = log->CreateCut(&epoch, &position);
    if (ret) {
      std::cerr << "failed to create cut ret " << ret << std::endl;
      assert(0);
    }
    entry *e = &entries_[std::make_pair(pool, name)];
    e->seq = position;
  }

  virtual int CheckTail(uint64_t epoch, const std::string& pool,
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

  virtual int CheckTail(uint64_t epoch, const std::string& pool,
      const std::string& name, std::vector<uint64_t>& positions, size_t count)
  {
    assert(0);
  }

  virtual int CheckTail(uint64_t epoch, const std::string& pool,
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

  struct entry {
    std::atomic<uint64_t> seq;
    stream_index_t streams;
  };

  std::map<std::pair<std::string, std::string>, entry> entries_;
};

#endif
