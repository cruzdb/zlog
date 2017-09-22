set(libzlog_sources
  log_impl.cc
  stream.cc
  striper.cc
  aio.cc
  capi.cc
  ../port/stack_trace.cc)

add_library(libzlog SHARED ${libzlog_sources})

# TODO: no link rados
if(BUILD_CEPH_BACKEND)
  target_include_directories(libzlog
      PUBLIC ${LIBRADOS_INCLUDE_DIRS}
   )
   target_link_libraries(libzlog
      zlog_backend_ceph
      ${LIBRADOS_LIBRARIES}
      ${Boost_SYSTEM_LIBRARY}
   )
endif(BUILD_CEPH_BACKEND)

target_link_libraries(libzlog
    zlog_proto
    zlog_seqr
    ${Boost_SYSTEM_LIBRARY}
    ${Backtrace_LIBRARIES}
)

set_target_properties(libzlog PROPERTIES
  OUTPUT_NAME zlog
  VERSION 1.0.0
  SOVERSION 1)

install(TARGETS libzlog LIBRARY DESTINATION lib)

add_library(test_libzlog OBJECT test_libzlog.cc)
target_include_directories(test_libzlog
  PRIVATE $<TARGET_PROPERTY:gtest,INTERFACE_INCLUDE_DIRECTORIES>)
