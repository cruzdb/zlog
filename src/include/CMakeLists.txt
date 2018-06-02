install(FILES
    zlog/backend.h
    zlog/capi.h
    zlog/log.h
    zlog/slice.h
    zlog/stream.h
    zlog/options.h
    zlog/statistics.h
    zlog/mempool/mempool.h
    zlog/mempool/demangle.h
    zlog/cache.h
    zlog/eviction.h
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

set(eviction_hdrs
  zlog/eviction/lru.h
  zlog/eviction/arc.h)
install(FILES
  ${eviction_hdrs}
  DESTINATION include/zlog/eviction
)
  
