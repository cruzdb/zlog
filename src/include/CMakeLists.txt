install(FILES
    zlog/backend.h
    zlog/capi.h
    zlog/log.h
    zlog/slice.h
    zlog/stream.h
    DESTINATION include/zlog
)

install(FILES
    zlog/backend/lmdb.h
    DESTINATION include/zlog/backend
)
