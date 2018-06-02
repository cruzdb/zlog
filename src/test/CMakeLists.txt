add_executable(create_log_lmdb create_log_lmdb.cc)
target_link_libraries(create_log_lmdb libzlog)

add_executable(open_log_lmdb open_log_lmdb.cc)
target_link_libraries(open_log_lmdb libzlog)

add_executable(cache_test cache_test.cc)
target_link_libraries(cache_test libzlog)
