install(FILES
    zlog/backend.h
    zlog/capi.h
    zlog/db.h
    zlog/iterator.h
    zlog/log.h
    zlog/slice.h
    zlog/stream.h
    zlog/transaction.h
    DESTINATION include/zlog
)

install(FILES
    zlog/backend/lmdb.h
    DESTINATION include/zlog/backend
)
