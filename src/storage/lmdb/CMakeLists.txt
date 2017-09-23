add_library(zlog_backend_lmdb SHARED lmdb.cc)
target_link_libraries(zlog_backend_lmdb lmdb)
set_target_properties(zlog_backend_lmdb PROPERTIES
  OUTPUT_NAME zlog_backend_lmdb
  VERSION 1.0.0
  SOVERSION 1)
install(TARGETS zlog_backend_lmdb LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})

add_executable(zlog_test_backend_lmdb
  test_backend_lmdb.cc
  $<TARGET_OBJECTS:test_backend>
  $<TARGET_OBJECTS:test_libzlog>)
target_link_libraries(zlog_test_backend_lmdb
  ${Boost_SYSTEM_LIBRARY}
  libzlog
  zlog_backend_lmdb
  gtest)
install(TARGETS zlog_test_backend_lmdb DESTINATION bin)

if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
  setup_target_for_coverage(zlog_test_backend_lmdb_coverage
    zlog_test_backend_lmdb coverage)
endif()
