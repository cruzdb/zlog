#ifndef LIBZLOG_ZLOG_HPP
#define LIBZLOG_ZLOG_HPP
#include "libseq/libseqr.h"
#include "zlog/stream.h"
#include "zlog/slice.h"
#include "zlog/backend.h"

namespace zlog {

class AioCompletion {
 public:
  virtual ~AioCompletion();
  virtual void SetCallback(std::function<void()> callback) = 0;
  virtual void WaitForComplete() = 0;
  virtual int ReturnValue() = 0;
};

class Log {
 public:
  Log() {}
  virtual ~Log();

  /*
   * Synchronous API
   */
  virtual int Append(const Slice& data, uint64_t *pposition = NULL) = 0;
  virtual int Read(uint64_t position, std::string *data) = 0;
  virtual int Fill(uint64_t position) = 0;
  virtual int CheckTail(uint64_t *pposition) = 0;
  virtual int Trim(uint64_t position) = 0;

  /*
   * Asynchronous API
   */
  virtual int AioAppend(AioCompletion *c, const Slice& data, uint64_t *pposition = NULL) = 0;
  virtual int AioRead(uint64_t position, AioCompletion *c, std::string *datap) = 0;

  static AioCompletion *aio_create_completion();
  static AioCompletion *aio_create_completion(
      std::function<void()> callback);

  /*
   * Stream API
   */
  virtual int OpenStream(uint64_t stream_id, Stream **streamptr) = 0;
  virtual int MultiAppend(const Slice& data,
      const std::set<uint64_t>& stream_ids, uint64_t *pposition = NULL) = 0;
  virtual int StreamMembership(std::set<uint64_t>& stream_ids, uint64_t position) = 0;

  /*
   * Log Management
   */

  virtual int StripeWidth() = 0;

  static int Create(const std::string& scheme, const std::string& name,
      const std::map<std::string, std::string>& params, SeqrClient *seqr,
      Log **log);

  static int Open(const std::string& scheme, const std::string& name,
      const std::map<std::string, std::string>& params, SeqrClient *seqr,
      Log **log);

  static int CreateWithStripeWidth(Backend *backend, const std::string& name,
      SeqrClient *seqr, int stripe_width, Log **logptr);

  static int Create(Backend *backend, const std::string& name,
      SeqrClient *seqr, Log **logptr);

  static int Open(Backend *backend, const std::string& name,
      SeqrClient *seqr, Log **logptr);

  // TODO remove, or move to backend?
  static int OpenOrCreate(Backend *backend, const std::string& name,
      SeqrClient *seqr, Log **logptr) {
    int ret = Open(backend, name, seqr, logptr);
    if (ret != -ENOENT)
      return ret;
    return Create(backend, name, seqr, logptr);
  }

 private:
  Log(const Log&);
  void operator=(const Log&);
};

}

#endif
