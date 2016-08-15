add_subdirectory(backend)

set(libzlog_sources
  log_impl.cc
  stream.cc
  stripe_history.cc
  log_mapper.cc
  aio.cc)

add_library(libzlog SHARED ${libzlog_sources})

#if(BUILD_CEPH_BACKEND)
#  list(APPEND libzlog_sources libzlog/capi.cc)
#  target_include_directories(libzlog
#      PUBLIC ${LIBRADOS_INCLUDE_DIRS}
#      PUBLIC ${LIBCLS_ZLOG_CLIENT_INCLUDE_DIRS}
#   )
#   target_link_libraries(libzlog
#      ${LIBRADOS_LIBRARIES}
#      ${LIBCLS_ZLOG_CLIENT_LIBRARIES}
#   )
#endif(BUILD_CEPH_BACKEND)

target_link_libraries(libzlog
    zlog_proto
    ${Boost_SYSTEM_LIBRARY}
)

set_target_properties(libzlog PROPERTIES OUTPUT_NAME "zlog")
