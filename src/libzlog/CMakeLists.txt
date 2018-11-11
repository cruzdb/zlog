set(libzlog_sources
  log_impl.cc
  striper.cc
  capi.cc
  log.cc
  backend.cc
  cache.cc
  ../eviction/lru.cc
  ../eviction/arc.cc
  ../port/stack_trace.cc
  ../port/port_posix.cc
  ../util/random.cc
  ../util/thread_local.cc
  ../monitoring/statistics.cc
  ../monitoring/histogram.cc
  ../util/mempool.cc
  )

#set_source_files_properties(../civetweb/src/civetweb.c PROPERTIES COMPILE_FLAGS -Wno-error)

add_definitions("-DZLOG_LIBDIR=\"${CMAKE_INSTALL_FULL_LIBDIR}\"")
add_definitions("-DCMAKE_SHARED_LIBRARY_SUFFIX=\"${CMAKE_SHARED_LIBRARY_SUFFIX}\"")
add_definitions("-DCMAKE_SHARED_LIBRARY_PREFIX=\"${CMAKE_SHARED_LIBRARY_PREFIX}\"")

add_library(libzlog SHARED ${libzlog_sources})

target_link_libraries(libzlog
    zlog_proto
    dl
    ${Boost_SYSTEM_LIBRARY}
    ${Backtrace_LIBRARIES}
)

set_target_properties(libzlog PROPERTIES
  OUTPUT_NAME zlog
  VERSION 1.0.0
  SOVERSION 1)

install(TARGETS libzlog LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})

add_library(test_libzlog OBJECT test_libzlog.cc)
target_include_directories(test_libzlog
  PRIVATE $<TARGET_PROPERTY:gtest,INTERFACE_INCLUDE_DIRECTORIES>)
