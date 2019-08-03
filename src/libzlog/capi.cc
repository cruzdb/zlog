#include <cerrno>
#include <cstring>
#include "include/zlog/log.h"
#include "include/zlog/capi.h"

extern "C" {

struct zlog_log_t {
  zlog::Log *rep;
};

struct zlog_options_t {
  zlog::Options rep;
};


int zlog_open(zlog_options_t *options, const char *name, zlog_log_t **log)
{
  zlog::Log *l;
  int ret = zlog::Log::Open(options->rep, name, &l);
  if (ret) {
    return ret;
  }

  auto result = new zlog_log_t;
  result->rep = l;
  *log = result;

  return 0;
}

void zlog_destroy(zlog_log_t *log)
{
  delete log->rep;
  delete log;
}

int zlog_checktail(zlog_log_t *log, uint64_t *pposition)
{
  return log->rep->tail(pposition);
}

int zlog_append(zlog_log_t *log, const char *data, size_t len, uint64_t *pposition)
{
  return log->rep->append(std::string(data, len), pposition);
}

ssize_t zlog_read(zlog_log_t *log, uint64_t position, char *data, size_t len)
{
  std::string blob;
  int ret = log->rep->read(position, &blob);
  if (ret) {
    return ret;
  }

  if (blob.size() > len) {
    return -ERANGE;
  }

  return blob.copy(data, blob.size(), 0);
}

int zlog_fill(zlog_log_t *log, uint64_t position)
{
  return log->rep->fill(position);
}

int zlog_trim(zlog_log_t *log, uint64_t position)
{
  return log->rep->trim(position);
}

int zlog_trim_to(zlog_log_t *log, uint64_t position)
{
  return log->rep->trimTo(position);
}

zlog_options_t *zlog_options_create(void)
{
  return new zlog_options_t;
}

void zlog_options_destroy(zlog_options_t *opts)
{
  delete opts;
}

void zlog_options_set_backend_name(zlog_options_t *opts, const char *name)
{
  opts->rep.backend_name = std::string(name);
}

void zlog_options_set_backend_option(zlog_options_t *opts, const char *name, const char *value)
{
  opts->rep.backend_options[name] = value;
}

void zlog_options_set_create_if_missing(zlog_options_t *opts, unsigned char v)
{
  opts->rep.create_if_missing = v;
}

void zlog_options_set_error_if_exists(zlog_options_t *opts, unsigned char v)
{
  opts->rep.error_if_exists = v;
}

}
