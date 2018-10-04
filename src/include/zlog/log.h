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
  virtual int Append(const Slice& data, uint64_t *pposition) = 0;
  virtual int Read(uint64_t position, std::string *data) = 0;
  virtual int Fill(uint64_t position) = 0;
  virtual int CheckTail(uint64_t *pposition) = 0;
  virtual int Trim(uint64_t position) = 0;

  /*
   * Asynchronous API
   */
  virtual int AioAppend(AioCompletion *c, const Slice& data, uint64_t *pposition) = 0;
  virtual int AioRead(uint64_t position, AioCompletion *c, std::string *datap) = 0;

  static AioCompletion *aio_create_completion();
  static AioCompletion *aio_create_completion(
      std::function<void()> callback);

  /*
   * Log Management
   */
 public:
  virtual int StripeWidth() = 0;

 public:
  static int Open(const Options& options,
      const std::string& name, Log **log);

 private:
  Log(const Log&);
  void operator=(const Log&);
};

}
