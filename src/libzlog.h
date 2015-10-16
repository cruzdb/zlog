#ifndef LIBZLOG_ZLOG_H
#define LIBZLOG_ZLOG_H

#include <rados/librados.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef void *zlog_log_t;

/*
 *
 */
int zlog_create(rados_ioctx_t ioctx, const char *name,
    int stripe_size, const char *host, const char *port,
    zlog_log_t *log);

/*
 *
 */
int zlog_open(rados_ioctx_t ioctx, const char *name,
    const char *host, const char *port,
    zlog_log_t *log);

/*
 *
 */
int zlog_open_or_create(rados_ioctx_t ioctx, const char *name,
    int stripe_size, const char *host, const char *port,
    zlog_log_t *log);

/*
 *
 */
int zlog_destroy(zlog_log_t log);

/*
 *
 */
int zlog_checktail(zlog_log_t log, uint64_t *pposition, int next);

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

#ifdef __cplusplus
}
#endif

#endif
