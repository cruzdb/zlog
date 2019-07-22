#pragma once
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct zlog_log_t zlog_log_t;
typedef struct zlog_options_t zlog_options_t;

extern int zlog_open(zlog_options_t *options, const char *name, zlog_log_t **log);
extern void zlog_destroy(zlog_log_t *log);
extern int zlog_checktail(zlog_log_t *log, uint64_t *pposition);
extern int zlog_append(zlog_log_t *log, const char *data, size_t len, uint64_t *pposition);
extern ssize_t zlog_read(zlog_log_t *log, uint64_t position, char *data, size_t len);
extern int zlog_fill(zlog_log_t *log, uint64_t position);
extern int zlog_trim(zlog_log_t *log, uint64_t position);
extern int zlog_trim_to(zlog_log_t *log, uint64_t position);

extern zlog_options_t *zlog_options_create(void);
extern void zlog_options_destroy(zlog_options_t *opts);
extern void zlog_options_set_backend_name(zlog_options_t *opts, const char *name);
extern void zlog_options_set_backend_option(zlog_options_t *opts, const char *name, const char *value);
extern void zlog_options_set_create_if_missing(zlog_options_t *opts, unsigned char v);
extern void zlog_options_set_error_if_exists(zlog_options_t *opts, unsigned char v);

#ifdef __cplusplus
}
#endif
