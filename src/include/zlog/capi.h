#pragma once
#include "zlog/backend.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef void *zlog_log_t;
typedef void *zlog_stream_t;
typedef void *zlog_options_t;

int zlog_create(zlog_options_t options, const char *scheme, const char *name,
    char const* const* keys, char const* const* vals, size_t num,
    const char *host, const char *port, zlog_log_t *log);

/*
 *
 */
int zlog_destroy(zlog_log_t log);

/*
 *
 */
int zlog_checktail(zlog_log_t log, uint64_t *pposition);

/*
 *
 */
int zlog_append(zlog_log_t log, const void *data, size_t len, uint64_t *pposition);

/*
 *
 */
int zlog_read(zlog_log_t log, uint64_t position, void *data, size_t len);

/*
 *
 */
int zlog_fill(zlog_log_t log, uint64_t position);

/*
 *
 */
int zlog_trim(zlog_log_t log, uint64_t position);

#ifdef __cplusplus
}
#endif
