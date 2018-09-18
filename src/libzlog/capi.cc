#include <cerrno>
#include "include/zlog/slice.h"
#include "include/zlog/stream.h"
#include "include/zlog/log.h"
#include "include/zlog/capi.h"

namespace zlog {

struct zlog_log_ctx {
  zlog::Log *log;
};

struct zlog_stream_ctx {
  zlog::Stream *stream;
  zlog_log_ctx *log_ctx;
};

extern "C" int zlog_destroy(zlog_log_t log)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  delete ctx->log;
  delete ctx;
  return 0;
}

extern "C" int zlog_create(zlog_options_t options, const char *scheme, const char *name,
    char const* const* keys, char const* const* vals, size_t num,
    const char *host, const char *port, zlog_log_t *log)
{
  std::map<std::string, std::string> opts;
  for (size_t i = 0; i < num; i++) {
    opts.emplace(keys[i], vals[i]);
  }

  zlog_log_ctx *ctx = new zlog_log_ctx;
  Options* op = (Options*)options;
  int ret = zlog::Log::Create(*op, scheme, name,
      opts, host, port, &ctx->log);
  if (ret) {
    delete ctx;
  } else {
    *log = ctx;
  }

  return ret;
}

extern "C" int zlog_checktail(zlog_log_t log, uint64_t *pposition)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  return ctx->log->CheckTail(pposition);
}

extern "C" int zlog_append(zlog_log_t log, const void *data, size_t len,
    uint64_t *pposition)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  return ctx->log->Append(Slice((char*)data, len), pposition);
}

extern "C" int zlog_read(zlog_log_t log, uint64_t position, void *data,
    size_t len)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  std::string entry;
  int ret = ctx->log->Read(position, &entry);
  if (ret >= 0) {
    if (entry.size() > len)
      return -ERANGE;
    memcpy(data, entry.data(), entry.size());
    ret = entry.size();
  }
  return ret;
}

extern "C" int zlog_fill(zlog_log_t log, uint64_t position)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  return ctx->log->Fill(position);
}

extern "C" int zlog_trim(zlog_log_t log, uint64_t position)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  return ctx->log->Trim(position);
}

}
