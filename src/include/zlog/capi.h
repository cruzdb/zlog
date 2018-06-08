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
int zlog_multiappend(zlog_log_t log, const void *data, size_t data_len,
    const uint64_t *stream_ids, size_t stream_ids_len,
    uint64_t *pposition);

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

#ifdef STREAMING_SUPPORT
/*
 *
 */
int zlog_stream_open(zlog_log_t log, uint64_t stream_id,
    zlog_stream_t *pstream);

/*
 *
 */
int zlog_stream_append(zlog_stream_t stream, const void *data, size_t len,
    uint64_t *pposition);

/*
 *
 */
int zlog_stream_readnext(zlog_stream_t stream, void *data, size_t len,
    uint64_t *pposition);

/*
 *
 */
int zlog_stream_reset(zlog_stream_t stream);

/*
 *
 */
int zlog_stream_sync(zlog_stream_t stream);

/*
 *
 */
uint64_t zlog_stream_id(zlog_stream_t stream);

/*
 *
 */
size_t zlog_stream_history(zlog_stream_t stream, uint64_t *pos, size_t len);

/*
 *
 */
int zlog_stream_membership(zlog_log_t log, uint64_t *stream_ids,
    size_t len, uint64_t position);
#endif

#ifdef __cplusplus
}
#endif
