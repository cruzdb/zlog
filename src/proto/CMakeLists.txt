PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS zlog.proto)
add_library(zlog_proto SHARED ${PROTO_SRCS} ${PROTO_HDRS})
target_link_libraries(zlog_proto
    ${PROTOBUF_LIBRARIES}
)
target_include_directories(zlog_proto
    PUBLIC ${PROTOBUF_INCLUDE_DIR}
)
install(TARGETS zlog_proto DESTINATION lib)

if(BUILD_CEPH_BACKEND)
PROTOBUF_GENERATE_CPP(BENCH_PROTO_SRCS BENCH_PROTO_HDRS adapter_test.proto)
add_executable(adapter_bench adapter_bench.cc ${BENCH_PROTO_SRCS}
  ${BENCH_PROTO_HDRS})
target_link_libraries(adapter_bench
  rados
  ${PROTOBUF_LIBRARIES}
)
target_include_directories(adapter_bench
  PUBLIC ${PROTOBUF_INCLUDE_DIR}
)
endif(BUILD_CEPH_BACKEND)
