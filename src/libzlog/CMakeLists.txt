add_subdirectory(backend)

set(libzlog_sources
  log_impl.cc
  stream.cc
  stripe_history.cc
  aio.cc
  backend/lmdb.cc)

if(BUILD_CEPH_BACKEND)
  list(APPEND libzlog_sources capi.cc)
endif(BUILD_CEPH_BACKEND)

add_library(libzlog SHARED ${libzlog_sources})

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
    ${LMDB_LIBRARIES}
)

set_target_properties(libzlog PROPERTIES OUTPUT_NAME "zlog")

install(TARGETS libzlog LIBRARY DESTINATION lib)
