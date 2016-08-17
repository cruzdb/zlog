PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS kvstore.proto)
add_library(kvstore_proto SHARED ${PROTO_SRCS} ${PROTO_HDRS})
target_link_libraries(kvstore_proto
    ${PROTOBUF_LIBRARIES}
)
target_include_directories(kvstore_proto
    PUBLIC ${PROTOBUF_INCLUDE_DIR}
)

add_library(libkvstore SHARED
    db_impl.cc
    transaction_impl.cc
    node_cache.cc
    iterator_impl.cc
)
target_link_libraries(libkvstore libzlog kvstore_proto)

add_executable(thrash thrash.cc)
target_link_libraries(thrash libzlog zlog_seqr libkvstore zlog_seqr)

add_executable(rbt rbt.cc)
target_link_libraries(rbt libkvstore zlog_seqr)
