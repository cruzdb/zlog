#ifndef LIBZLOG_ZLOG_HPP
#define LIBZLOG_ZLOG_HPP
#include <rados/librados.hpp>
#include "libseqr.h"

namespace zlog {

class Log {
 public:
  Log() {}

  struct AioCompletionImpl;

  class AioCompletion {
   public:
    typedef void *completion_t;
    typedef void (*callback_t)(completion_t cb, void *arg);
    AioCompletion(AioCompletionImpl *pc) : pc(pc) {}
    void set_callback(void *arg, callback_t cb);
    void wait_for_complete();
    int get_return_value();
    void release();
    void *pc;
  };

  /*
   * Set a new projection.
   */
  int SetProjection(uint64_t *pepoch);

  /*
   * Get the current projection.
   */
  int GetProjection(uint64_t *pepoch);

  /*
   * Find the maximum position written.
   */
  int FindMaxPosition(uint64_t epoch, bool *pempty, uint64_t *pposition);

  /*
   * Seal all storage devices.
   */
  int Seal(uint64_t epoch);

  /*
   * Find and optionally increment the current tail position.
   */
  int CheckTail(uint64_t *pposition, bool increment = false);

  /*
   * Return a batch of positions.
   */
  int CheckTail(std::vector<uint64_t>& positions, size_t count);

  /*
   * Append data to the log and return its position.
   */
  int Append(ceph::bufferlist& data, uint64_t *pposition = NULL);

  /*
   * Append data to multiple streams and return its position.
   */
  int MultiAppend(ceph::bufferlist& data,
      const std::set<uint64_t>& stream_ids, uint64_t *pposition = NULL);

  /*
   *
   */
  class Stream {
   public:
    Stream() : impl(NULL) {}
    int Append(ceph::bufferlist& data, uint64_t *pposition = NULL);
    int ReadNext(ceph::bufferlist& bl, uint64_t *pposition = NULL);
    int Reset();
    int Sync();
    uint64_t Id() const;

    std::vector<uint64_t> History() const;

   private:
    friend class Log;
    struct StreamImpl;
    StreamImpl *impl;
  };

  /*
   *
   */
  int OpenStream(uint64_t stream_id, Stream& stream);

  /*
   * Append data asynchronously to the log and return its position.
   */
  int AioAppend(AioCompletion *c, ceph::bufferlist& data,
      uint64_t *pposition = NULL);

  /*
   * Read data asynchronously from the log.
   */
  int AioRead(uint64_t position, AioCompletion *c,
      ceph::bufferlist *bpl);

  /*
   * Mark a position as unused.
   */
  int Fill(uint64_t position);

  /*
   *
   */
  int Read(uint64_t position, ceph::bufferlist& bl);

  /*
   *
   */
  int Trim(uint64_t position);
 
  /*
   *
   */
  int UpdateLayout(librados::IoCtx& ioctx, int stripe_size);

  /*
   * Create a new log.
   */
  static int Create(librados::IoCtx& ioctx, const std::string& name,
      int stripe_size, SeqrClient *seqr, Log& log);

  /*
   * Open an existing log.
   */
  static int Open(librados::IoCtx& ioctx, const std::string& name,
      SeqrClient *seqr, Log& log);

  /*
   * Open an existing log or create it if it doesn't exist.
   */
  static int OpenOrCreate(librados::IoCtx& ioctx, const std::string& name,
      int stripe_size, SeqrClient *seqr, Log& log) {
    int ret = Open(ioctx, name, seqr, log);
    if (ret != -ENOENT)
      return ret;
    ret = Create(ioctx, name, stripe_size, seqr, log);
    if (ret == 0)
      return Open(ioctx, name, seqr, log);
    return ret;
  }

  static AioCompletion *aio_create_completion();
  static AioCompletion *aio_create_completion(void *arg,
      zlog::Log::AioCompletion::callback_t cb);

  /*
   * Return the stream membership for a log entry position.
   */
  int StreamMembership(std::set<uint64_t>& stream_ids, uint64_t position);
  int StreamMembership(uint64_t epoch, std::set<uint64_t>& stream_ids, uint64_t position);
  int Fill(uint64_t epoch, uint64_t position);

 private:
  Log(const Log& rhs);
  Log& operator=(const Log& rhs);

  int RefreshProjection();

  int Read(uint64_t epoch, uint64_t position, ceph::bufferlist& bl);

  int StreamHeader(ceph::bufferlist& bl, std::set<uint64_t>& stream_ids,
      size_t *header_size = NULL);

  /*
   * When next == true
   *   - position: new log tail
   *   - stream_backpointers: back pointers for each stream in stream_ids
   *
   * When next == false
   *   - position: current log tail
   *   - stream_backpointers: back pointers for each stream in stream_ids
   */
  int CheckTail(const std::set<uint64_t>& stream_ids,
      std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
      uint64_t *position, bool next);

  static std::string metalog_oid_from_name(const std::string& name);
  std::string slot_to_oid(int i);
  std::string position_to_oid(uint64_t position);
  std::string position_to_oid_from_map(uint64_t position);

  librados::IoCtx *ioctx_;
  std::string pool_;
  std::string name_;
  std::string metalog_oid_;
  int stripe_size_;
  std::map<uint64_t, int> stripe_map_;
  SeqrClient *seqr;
  uint64_t epoch_;
};

}

#endif
