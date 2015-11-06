#ifndef LIBZLOG_INTERNAL_HPP
#define LIBZLOG_INTERNAL_HPP

#include <rados/librados.h>
#include "libzlog.hpp"
#include "libzlog.h"

struct zlog_log_ctx {
  librados::IoCtx ioctx;
  zlog::SeqrClient *seqr;
  zlog::Log log;
};

struct zlog_stream_ctx {
  zlog::Log::Stream stream;
  zlog_log_ctx *log_ctx;
};

#endif
