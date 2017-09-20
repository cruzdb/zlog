add_library(zlog_backend_lmdb lmdb.cc)

add_executable(zlog_test_backend_lmdb
  test_backend_lmdb.cc
  $<TARGET_OBJECTS:test_backend>
  $<TARGET_OBJECTS:test_libzlog>)
target_link_libraries(zlog_test_backend_lmdb
  ${Boost_SYSTEM_LIBRARY}
  libzlog
  zlog_backend_lmdb
  gtest_main)
install(TARGETS zlog_test_backend_lmdb DESTINATION bin)

if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
  setup_target_for_coverage(zlog_test_backend_lmdb_coverage
    zlog_test_backend_lmdb coverage)
endif()
