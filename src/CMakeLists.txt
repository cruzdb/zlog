PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS zlog.proto)
add_library(zlog_proto SHARED ${PROTO_SRCS} ${PROTO_HDRS})
target_link_libraries(zlog_proto
    ${PROTOBUF_LIBRARIES}
)

####

add_library(zlog_seqr SHARED
    libseqr.cc
)

target_link_libraries(zlog_seqr
    zlog_proto
)

####

add_library(zlog SHARED
    libzlog.cc
    stream.cc
    aio.cc
)

target_include_directories(zlog
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
    PUBLIC ${LIBCLS_ZLOG_CLIENT_INCLUDE_DIRS}
)

target_link_libraries(zlog
    zlog_proto
    ${LIBRADOS_LIBRARIES}
    ${LIBCLS_ZLOG_CLIENT_LIBRARIES}
)

####

add_library(zstate SHARED
    zstate/skytype.cc
)

target_link_libraries(zstate
    zlog
)

####

add_executable(zlog-seqr
    seqr-server.cc
)

target_link_libraries(zlog-seqr
    zlog
    zlog_proto
    zlog_seqr
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

####

add_executable(zlog-seqr-bench
    zlog-seqr-bench.cc
)

target_link_libraries(zlog-seqr-bench
    zlog
    zlog_seqr
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

####

add_executable(zlog-bench-ng
    zlog-bench-ng.cc
)

target_link_libraries(zlog-bench-ng
    zlog
    zlog_seqr
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
    atomic
)

####

add_executable(stream-stress
    stream-stress.cc
)

target_link_libraries(stream-stress
    zlog
    zlog_seqr
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

####

add_library(gtest
    gtest/src/gtest-all.cc
    gtest/src/gtest_main.cc
)

target_include_directories(gtest
    PUBLIC gtest/include
    PRIVATE gtest
)

####

add_executable(zlog-test
    test.cc
)

target_link_libraries(zlog-test
    zlog
    gtest
    zlog_seqr
    ${Boost_SYSTEM_LIBRARY}
)

####

add_executable(zstate-test
    zstate/test.cc
)

target_link_libraries(zstate-test
    zlog
    gtest
    zstate
    zlog_seqr
    ${Boost_SYSTEM_LIBRARY}
)
