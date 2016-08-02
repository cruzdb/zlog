PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS kvstore.proto)
add_library(kvstore_proto SHARED ${PROTO_SRCS} ${PROTO_HDRS})
target_link_libraries(kvstore_proto
    ${PROTOBUF_LIBRARIES}
)

add_library(libkvstore SHARED
    db.cc
    transaction.cc
    node_cache.cc
    iterator.cc
)
target_link_libraries(libkvstore libzlog kvstore_proto)

add_executable(thrash thrash.cc)
target_link_libraries(thrash libzlog zlog_seqr libkvstore)

add_executable(db_test db_test.cc)
target_link_libraries(db_test libkvstore)

add_executable(rbt rbt.cc)
target_link_libraries(rbt libkvstore)

add_executable(iterator_test iterator_test.cc)
target_link_libraries(iterator_test libkvstore)

if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    include(CodeCoverage)
    setup_target_for_coverage(thrash_coverage thrash coverage)
endif()
