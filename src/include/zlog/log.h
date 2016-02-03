#ifndef LIBZLOG_ZLOG_HPP
#define LIBZLOG_ZLOG_HPP
#include <rados/librados.hpp>
#include "libseq/libseqr.h"

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
   * Synchronous API
   */
  virtual int Append(ceph::bufferlist& data, uint64_t *pposition = NULL) = 0;
  virtual int Read(uint64_t position, ceph::bufferlist& bl) = 0;
  virtual int Fill(uint64_t position) = 0;
  virtual int CheckTail(uint64_t *pposition) = 0;
  virtual int Trim(uint64_t position) = 0;

  /*
   * Asynchronous API
   */
  virtual int AioAppend(AioCompletion *c, ceph::bufferlist& data, uint64_t *pposition = NULL) = 0;
  virtual int AioRead(uint64_t position, AioCompletion *c, ceph::bufferlist *bpl) = 0;

  static AioCompletion *aio_create_completion();
  static AioCompletion *aio_create_completion(void *arg,
      zlog::Log::AioCompletion::callback_t cb);

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
    friend class LogImpl;
    class StreamImpl;
    StreamImpl *impl;
  };

  virtual int OpenStream(uint64_t stream_id, Stream **streamptr) = 0;
  virtual int MultiAppend(ceph::bufferlist& data,
      const std::set<uint64_t>& stream_ids, uint64_t *pposition = NULL) = 0;
  virtual int StreamMembership(std::set<uint64_t>& stream_ids, uint64_t position) = 0;

  /*
   * Log Management
   */

  static int Create(librados::IoCtx& ioctx, const std::string& name,
      SeqrClient *seqr, Log **logptr);

  static int Open(librados::IoCtx& ioctx, const std::string& name,
      SeqrClient *seqr, Log **logptr);

  static int OpenOrCreate(librados::IoCtx& ioctx, const std::string& name,
      SeqrClient *seqr, Log **logptr) {
    int ret = Open(ioctx, name, seqr, logptr);
    if (ret != -ENOENT)
      return ret;
    return Create(ioctx, name, seqr, logptr);
  }

 private:
  Log(const Log&);
  void operator=(const Log&);
};

}

#endif
