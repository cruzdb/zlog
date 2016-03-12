#ifndef ZLOG_SRC_BENCH_COMMON_H
#define ZLOG_SRC_BENCH_COMMON_H

static inline uint64_t __getns(clockid_t clock)
{
  struct timespec ts;
  int ret = clock_gettime(clock, &ts);
  assert(ret == 0);
  return (((uint64_t)ts.tv_sec) * 1000000000ULL) + ts.tv_nsec;
}

static inline uint64_t getns()
{
  return __getns(CLOCK_MONOTONIC);
}


#endif
