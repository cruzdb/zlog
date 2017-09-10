add_subdirectory(ceph)

add_library(test_backend OBJECT test_backend.cc)
target_include_directories(test_backend
  PRIVATE $<TARGET_PROPERTY:gtest,INTERFACE_INCLUDE_DIRECTORIES>)

add_executable(zlog_test_backend_lmdb test_backend_lmdb.cc)
target_link_libraries(zlog_test_backend_lmdb
  $<TARGET_OBJECTS:test_backend>
  $<TARGET_OBJECTS:test_libzlog>
  ${Boost_SYSTEM_LIBRARY}
  libzlog
  gtest_main)
