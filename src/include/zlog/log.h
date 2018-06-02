#pragma once
#include <functional>
#include <map>
#include <memory>
#include <set>
#include <string>
#include "slice.h"
#include "options.h"

namespace zlog {

class Backend;
#if STREAMING_SUPPORT
class Stream;
#endif

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
#if STREAMING_SUPPORT
  virtual int OpenStream(uint64_t stream_id, Stream **streamptr) = 0;
  virtual int MultiAppend(const Slice& data,
      const std::set<uint64_t>& stream_ids, uint64_t *pposition = NULL) = 0;
  virtual int StreamMembership(std::set<uint64_t>& stream_ids, uint64_t position) = 0;
#endif

  /*
   * Log Management
   */
 public:
  virtual int StripeWidth() = 0;

 public:
  static int Create(const Options& options, const std::string& scheme,
      const std::string& name,
      const std::map<std::string, std::string>& params,
      const std::string& host, const std::string& port,
      Log **log);

  static int Open(const Options& options, const std::string& scheme,
      const std::string& name,
      const std::map<std::string, std::string>& params,
      const std::string& host, const std::string& port,
      Log **log);

 public:
  // TODO: open/create if already shared, or if exclusive force?
  static int CreateWithBackend(const Options& options,
      std::shared_ptr<Backend> backend,
      const std::string& name, Log **logptr);

  static int OpenWithBackend(const Options& options,
      std::shared_ptr<Backend> backend,
      const std::string& name, Log **logptr);
  


 private:
  Log(const Log&);
  void operator=(const Log&);

};

}
