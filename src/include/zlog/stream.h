#pragma once
#include <vector>
#include "zlog/slice.h"

namespace zlog {

class Stream {
 public:
  virtual ~Stream();
  virtual std::vector<uint64_t> History() const = 0;
  virtual int ReadNext(std::string *data, uint64_t *pposition = NULL) = 0;
  virtual int Append(const Slice& data, uint64_t *pposition = NULL) = 0;
  virtual int Reset() = 0;
  virtual int Sync() = 0;
  virtual uint64_t Id() const = 0;
};

}
