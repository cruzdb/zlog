PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS zlog.proto)

set(libzlog_sources
  log_impl.cc
  striper.cc
  capi.cc
  log.cc
  backend.cc
  cache.cc
  stripe.cc
  object_map.cc
  ../eviction/lru.cc
  ../eviction/arc.cc
  ../port/stack_trace.cc
  ../port/port_posix.cc
  ../util/random.cc
  ../util/thread_local.cc
  ../monitoring/statistics.cc
  ../monitoring/histogram.cc
  ../util/mempool.cc
  ${PROTO_SRCS}
  ${PROTO_HDRS})

add_definitions("-DZLOG_LIBDIR=\"${CMAKE_INSTALL_FULL_LIBDIR}\"")
add_definitions("-DCMAKE_SHARED_LIBRARY_SUFFIX=\"${CMAKE_SHARED_LIBRARY_SUFFIX}\"")
add_definitions("-DCMAKE_SHARED_LIBRARY_PREFIX=\"${CMAKE_SHARED_LIBRARY_PREFIX}\"")

add_library(libzlog SHARED ${libzlog_sources})

target_include_directories(libzlog
  PRIVATE ${PROTOBUF_INCLUDE_DIR})

target_link_libraries(libzlog
    dl
    ${PROTOBUF_LIBRARIES}
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
  PUBLIC ${Boost_INCLUDE_DIRS}
  PRIVATE $<TARGET_PROPERTY:gtest,INTERFACE_INCLUDE_DIRECTORIES>)
