if(BUILD_CEPH_BACKEND)
add_library(zlog_backend_ceph SHARED ceph.cc)
target_link_libraries(zlog_backend_ceph
    zlog_proto ${LIBCLS_ZLOG_CLIENT_LIBRARIES}
    ${LIBRADOS_LIBRARIES})
target_include_directories(zlog_backend_ceph
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
    PUBLIC ${LIBCLS_ZLOG_CLIENT_INCLUDE_DIRS}
)
install(TARGETS zlog_backend_ceph DESTINATION lib)
endif(BUILD_CEPH_BACKEND)
