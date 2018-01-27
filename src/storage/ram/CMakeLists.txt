add_library(zlog_backend_ram SHARED ram.cc)
set_target_properties(zlog_backend_ram PROPERTIES
  OUTPUT_NAME zlog_backend_ram
  VERSION 1.0.0
  SOVERSION 1)
install(TARGETS zlog_backend_ram LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})

add_executable(zlog_test_backend_ram
  test_backend_ram.cc
  $<TARGET_OBJECTS:test_backend>
  $<TARGET_OBJECTS:test_libzlog>)
target_link_libraries(zlog_test_backend_ram
  ${Boost_SYSTEM_LIBRARY}
  libzlog
  zlog_backend_ram
  gtest)
install(TARGETS zlog_test_backend_ram DESTINATION bin)

if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
  setup_target_for_coverage(zlog_test_backend_ram_coverage
    zlog_test_backend_ram coverage)
endif()
