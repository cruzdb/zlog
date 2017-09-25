PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS zlog.proto)
add_library(zlog_proto SHARED ${PROTO_SRCS} ${PROTO_HDRS})
target_link_libraries(zlog_proto
    ${PROTOBUF_LIBRARIES}
)
target_include_directories(zlog_proto
    PUBLIC ${PROTOBUF_INCLUDE_DIR}
)
install(TARGETS zlog_proto DESTINATION ${CMAKE_INSTALL_LIBDIR})
