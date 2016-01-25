#ifndef LIBZLOG_ZLOG_HPP
#define LIBZLOG_ZLOG_HPP
#include <rados/librados.hpp>
#include "libseqr.h"

namespace zlog {

class LogHL {
 public:
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
   * Synchronous API
   */
  int Append(ceph::bufferlist& data, uint64_t *pposition = NULL);
  int Read(uint64_t position, ceph::bufferlist& bl);
  int Fill(uint64_t position);
  int CheckTail(uint64_t *pposition);
  int Trim(uint64_t position);

  /*
   * Asynchronous API
   */
  int AioAppend(AioCompletion *c, ceph::bufferlist& data, uint64_t *pposition = NULL);
  int AioRead(uint64_t position, AioCompletion *c, ceph::bufferlist *bpl);

  static AioCompletion *aio_create_completion();
  static AioCompletion *aio_create_completion(void *arg,
      zlog::LogHL::AioCompletion::callback_t cb);

  /*
   * Stream API
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
    friend class LogHL;
    class StreamImpl;
    StreamImpl *impl;
  };

  int OpenStream(uint64_t stream_id, Stream& stream);
  int MultiAppend(ceph::bufferlist& data,
      const std::set<uint64_t>& stream_ids, uint64_t *pposition = NULL);
  int StreamMembership(std::set<uint64_t>& stream_ids, uint64_t position);

  /*
   * Log Management
   */

  static int Create(librados::IoCtx& ioctx, const std::string& name,
      int stripe_size, SeqrClient *seqr, LogHL& log);

  static int Open(librados::IoCtx& ioctx, const std::string& name,
      SeqrClient *seqr, LogHL& log);

  static int OpenOrCreate(librados::IoCtx& ioctx, const std::string& name,
      int stripe_size, SeqrClient *seqr, LogHL& log) {
    int ret = Open(ioctx, name, seqr, log);
    if (ret != -ENOENT)
      return ret;
    ret = Create(ioctx, name, stripe_size, seqr, log);
    if (ret == 0)
      return Open(ioctx, name, seqr, log);
    return ret;
  }

 private:
  class LogHLImpl;
  LogHLImpl *impl;
};

}

#endif
