#pragma once
#include <functional>
#include <map>
#include <memory>
#include <set>
#include <string>
#include "options.h"

namespace zlog {

class Backend;

class Log {
 public:
  Log() {}
  virtual ~Log();

  /**
   *
   */
  virtual int CheckTail(uint64_t *pposition) = 0;
  virtual int tailAsync(std::function<void(int, uint64_t)> cb) = 0;

  /**
   *
   */
  virtual int Append(const std::string& data, uint64_t *pposition) = 0;
  virtual int appendAsync(const std::string& data,
      std::function<void(int, uint64_t)> cb) = 0;

  /**
   *
   */
  virtual int Read(uint64_t position, std::string *data) = 0;
  virtual int readAsync(uint64_t position,
      std::function<void(int, std::string&)> cb) = 0;

  /**
   *
   */
  virtual int Fill(uint64_t position) = 0;
  virtual int fillAsync(uint64_t position, std::function<void(int)> cb) = 0;

  /**
   *
   */
  virtual int Trim(uint64_t position) = 0;
  virtual int trimAsync(uint64_t position, std::function<void(int)> cb) = 0;

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
