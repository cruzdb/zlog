#ifndef LIBZLOG_INTERNAL_HPP
#define LIBZLOG_INTERNAL_HPP
#include <mutex>
#include <rados/librados.h>
#include "include/zlog/log.h"
#include "libseq/libseqr.h"
#include "log_mapper.h"
#include "backend.h"

namespace zlog {

class LogImpl : public Log {
 public:
  LogImpl() : backend(NULL) {}

  /*
   * Create cut.
   */
  int CreateCut(uint64_t *pepoch, uint64_t *maxpos);

  /*
   * Set log stripe width
   */
  int SetStripeWidth(int width);

  /*
   * Find and optionally increment the current tail position.
   */
  int CheckTail(uint64_t *pposition, bool increment);
  int CheckTail(uint64_t *pposition);

  /*
   * Return a batch of positions.
   */
  int CheckTail(std::vector<uint64_t>& positions, size_t count);

  /*
   * Append data to the log and return its position.
   */
  int Append(ceph::bufferlist& data, uint64_t *pposition = NULL);

  int OpenStream(uint64_t stream_id, zlog::Stream **streamptr);

  /*
   * Append data to multiple streams and return its position.
   */
  int MultiAppend(ceph::bufferlist& data,
      const std::set<uint64_t>& stream_ids, uint64_t *pposition = NULL);

  /*
   * Append data asynchronously to the log and return its position.
   */
  int AioAppend(zlog::AioCompletion *c, ceph::bufferlist& data,
      uint64_t *pposition = NULL);

  /*
   * Read data asynchronously from the log.
   */
  int AioRead(uint64_t position, zlog::AioCompletion *c,
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
   * Return the stream membership for a log entry position.
   */
  int StreamMembership(std::set<uint64_t>& stream_ids, uint64_t position);
  int StreamMembership(uint64_t epoch, std::set<uint64_t>& stream_ids, uint64_t position);
  int Fill(uint64_t epoch, uint64_t position);

  // Seal an epoch across a set of objects and return the next position.
  int Seal(const std::vector<std::string>& objects,
      uint64_t epoch, uint64_t *next_pos);

  static std::string metalog_oid_from_name(const std::string& name);

  LogImpl(const LogImpl& rhs);
  LogImpl& operator=(const LogImpl& rhs);

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

  int StripeWidth() const;

  librados::IoCtx *ioctx_;
  std::string pool_;
  std::string name_;
  std::string metalog_oid_;
  SeqrClient *seqr;

  Backend *backend;

  void set_backend_v2() {
    assert(backend);
    delete backend;
    backend = Backend::CreateV2();
  }

  /*
   *
   */
  std::mutex lock_;
  LogMapper mapper_;
  uint64_t epoch_;
};

struct zlog_log_ctx {
  librados::IoCtx ioctx;
  zlog::SeqrClient *seqr;
  zlog::Log *log;
};

struct zlog_stream_ctx {
  zlog::Stream *stream;
  zlog_log_ctx *log_ctx;
};


}

#endif
