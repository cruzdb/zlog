#ifndef LIBZLOG_ZLOG_H
#define LIBZLOG_ZLOG_H

namespace zlog {
class Log {
 public:
  /*
   * Create a new log.
   */
  static int Create(librados::IoCtx& ioctx, const std::string& name,
      int stripe_size, Log **log);

 private:
  Log() {}
  Log(const Log& rhs);
  Log& operator=(const Log& rhs);

  librados::IoCtx *ioctx_;
  std::string name_;
  std::string metalog_oid_;
  int stripe_size_;
};
}

#endif
