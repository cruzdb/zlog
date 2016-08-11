#ifndef ZLOG_INCLUDE_ZLOG_BACKEND_H
#define ZLOG_INCLUDE_ZLOG_BACKEND_H

class Backend {
 public:
  explicit Backend(void *ioctx) : ioctx(ioctx) {}
  void *ioctx;
};

#endif
