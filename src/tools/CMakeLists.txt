add_executable(kvs-export kvs-export.cc)
target_link_libraries(kvs-export libkvstore zlog_seqr zlog_seqr
  zlog_backend_lmdb)
