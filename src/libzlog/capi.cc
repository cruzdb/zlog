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

#ifdef STREAMING_SUPPORT
extern "C" int zlog_multiappend(zlog_log_t log, const void *data,
    size_t data_len, const uint64_t *stream_ids, size_t stream_ids_len,
    uint64_t *pposition)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;
  if (stream_ids_len == 0)
    return -EINVAL;
  std::set<uint64_t> ids(stream_ids, stream_ids + stream_ids_len);
  return ctx->log->MultiAppend(Slice((char*)data, data_len), ids, pposition);
}

extern "C" int zlog_stream_open(zlog_log_t log, uint64_t stream_id,
    zlog_stream_t *pstream)
{
  zlog_log_ctx *log_ctx = (zlog_log_ctx*)log;

  zlog_stream_ctx *stream_ctx = new zlog_stream_ctx;
  stream_ctx->log_ctx = log_ctx;

  int ret = log_ctx->log->OpenStream(stream_id, &stream_ctx->stream);
  if (ret) {
    delete stream_ctx;
    return ret;
  }

  *pstream = stream_ctx;

  return 0;
}

extern "C" int zlog_stream_append(zlog_stream_t stream, const void *data,
    size_t len, uint64_t *pposition)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;
  return ctx->stream->Append(Slice((char*)data, len), pposition);
}

extern "C" int zlog_stream_readnext(zlog_stream_t stream, void *data,
    size_t len, uint64_t *pposition)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;

  std::string entry;
  int ret = ctx->stream->ReadNext(&entry, pposition);

  if (ret >= 0) {
    if (entry.size() > len)
      return -ERANGE;
    memcpy(data, entry.data(), entry.size());
    ret = entry.size();
  }

  return ret;
}

extern "C" int zlog_stream_reset(zlog_stream_t stream)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;
  return ctx->stream->Reset();
}

extern "C" int zlog_stream_sync(zlog_stream_t stream)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;
  return ctx->stream->Sync();
}

extern "C" uint64_t zlog_stream_id(zlog_stream_t stream)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;
  return ctx->stream->Id();
}

extern "C" size_t zlog_stream_history(zlog_stream_t stream, uint64_t *pos, size_t len)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;

  std::vector<uint64_t> history = ctx->stream->History();
  size_t size = history.size();
  if (pos && size <= len)
    std::copy(history.begin(), history.end(), pos);

  return size;
}

extern "C" int zlog_stream_membership(zlog_log_t log,
    uint64_t *stream_ids, size_t len, uint64_t position)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;

  std::set<uint64_t> ids;
  int ret = ctx->log->StreamMembership(ids, position);
  if (ret)
    return ret;

  size_t size = ids.size();
  if (size <= len) {
    std::vector<uint64_t> tmp;
    for (auto it = ids.begin(); it != ids.end(); it++)
      tmp.push_back(*it);
    std::copy(tmp.begin(), tmp.end(), stream_ids);
  }

  return size;
}
#endif

}
