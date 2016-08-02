add_subdirectory(proto)
add_subdirectory(kvstore)
include_directories(${PROJECT_SOURCE_DIR}/src/include)

add_library(zlog_seqr SHARED libseq/libseqr.cc)
target_link_libraries(zlog_seqr zlog_proto)

####

add_library(libzlog SHARED
    libzlog/log_impl.cc
    libzlog/stream.cc
    libzlog/aio.cc
    libzlog/stripe_history.cc
    libzlog/log_mapper.cc
    libzlog/backend.cc
)

target_include_directories(libzlog
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
    PUBLIC ${LIBCLS_ZLOG_CLIENT_INCLUDE_DIRS}
)

target_link_libraries(libzlog
    zlog_proto
    ${LIBRADOS_LIBRARIES}
    ${LIBCLS_ZLOG_CLIENT_LIBRARIES}
)

set_target_properties(libzlog PROPERTIES OUTPUT_NAME "zlog")

####

add_library(zstate SHARED
    zstate/skytype.cc
)

target_link_libraries(zstate
    libzlog
)

####

add_executable(zlog-seqr
    seqr-server.cc
)

target_link_libraries(zlog-seqr
    libzlog
    zlog_proto
    zlog_seqr
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

####

add_executable(append-check append-check.cc)
target_link_libraries(append-check
    libzlog
    zlog_seqr
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

####

add_executable(zlogtool zlog-tool.cc)
set_target_properties(zlogtool PROPERTIES OUTPUT_NAME "zlog")
target_link_libraries(zlogtool
    libzlog
    zlog_seqr
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

####

add_executable(zlog-seqr-bench
    zlog-seqr-bench.cc
)

target_link_libraries(zlog-seqr-bench
    libzlog
    zlog_seqr
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

####

add_executable(zlog-bench-ng
    zlog-bench-ng.cc
)

target_link_libraries(zlog-bench-ng
    libzlog
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
    libzlog
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
    test/test.cc
    test/test_internal.cc
)

target_link_libraries(zlog-test
    libzlog
    gtest
    zlog_seqr
    ${Boost_SYSTEM_LIBRARY}
)

####

add_executable(zstate-test
    test/zstate_test.cc
)

target_link_libraries(zstate-test
    libzlog
    gtest
    zstate
    zlog_seqr
    ${Boost_SYSTEM_LIBRARY}
)
