add_subdirectory(ceph)

add_library(test_backend OBJECT test_backend.cc)
target_include_directories(test_backend
  PRIVATE $<TARGET_PROPERTY:gtest,INTERFACE_INCLUDE_DIRECTORIES>)

add_executable(zlog_test_lmdb_backend test_lmdb_backend.cc)
target_link_libraries(zlog_test_lmdb_backend
  $<TARGET_OBJECTS:test_backend>
  gtest_main)
