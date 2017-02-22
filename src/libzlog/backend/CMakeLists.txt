if(BUILD_CEPH_BACKEND)

PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS zlog.proto)
add_library(zlog_ceph_proto SHARED ${PROTO_SRCS} ${PROTO_HDRS})
target_link_libraries(zlog_ceph_proto
    ${PROTOBUF_LIBRARIES}
)
target_include_directories(zlog_ceph_proto
    PUBLIC ${PROTOBUF_INCLUDE_DIR}
)

add_library(cls_zlog_client SHARED cls_zlog_client.cc)
target_link_libraries(cls_zlog_client
    zlog_ceph_proto
    ${LIBRADOS_LIBRARIES})
target_include_directories(cls_zlog_client
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
)

add_library(zlog_backend_ceph SHARED ceph.cc)
target_link_libraries(zlog_backend_ceph
    zlog_proto
    cls_zlog_client
    ${LIBRADOS_LIBRARIES})
target_include_directories(zlog_backend_ceph
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
)
install(TARGETS zlog_backend_ceph DESTINATION lib)
endif(BUILD_CEPH_BACKEND)
