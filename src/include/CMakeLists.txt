install(FILES
    zlog/backend.h
    zlog/capi.h
    zlog/log.h
    zlog/slice.h
    zlog/stream.h
    zlog/options.h
    zlog/monitoring/statistics.h
    zlog/monitoring/histogram.h
    zlog/stats/statistics.h
    DESTINATION include/zlog
)

set(backend_hdrs
  zlog/backend/lmdb.h
  zlog/backend/ram.h)

if(BUILD_CEPH_BACKEND)
  list(APPEND backend_hdrs
    zlog/backend/ceph.h)
endif(BUILD_CEPH_BACKEND)

install(FILES
  ${backend_hdrs}
  DESTINATION include/zlog/backend
)
