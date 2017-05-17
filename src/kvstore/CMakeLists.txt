PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS kvstore.proto)
add_library(kvstore_proto SHARED ${PROTO_SRCS} ${PROTO_HDRS})
target_link_libraries(kvstore_proto
    ${PROTOBUF_LIBRARIES}
)
target_include_directories(kvstore_proto
    PUBLIC ${PROTOBUF_INCLUDE_DIR}
)
install(TARGETS kvstore_proto DESTINATION lib)

add_library(libkvstore SHARED
    db_impl.cc
    transaction_impl.cc
    node_cache.cc
    iterator_impl.cc
    node.cc
)
target_link_libraries(libkvstore libzlog kvstore_proto)
install(TARGETS libkvstore LIBRARY DESTINATION lib)

add_executable(thrash thrash.cc)
target_link_libraries(thrash libzlog zlog_seqr libkvstore zlog_seqr)

add_executable(rbt rbt.cc)
target_link_libraries(rbt libkvstore zlog_seqr)

add_executable(bench bench.cc)
target_link_libraries(bench libzlog zlog_seqr libkvstore zlog_seqr lmdb)
if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
  setup_target_for_coverage(bench-cov bench coverage "10000")
endif()
