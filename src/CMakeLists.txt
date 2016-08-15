add_subdirectory(proto)
include_directories(${PROJECT_SOURCE_DIR}/src/include)

add_library(zlog_seqr SHARED libseq/libseqr.cc)
target_link_libraries(zlog_seqr zlog_proto)

add_subdirectory(libzlog)
add_subdirectory(kvstore)
################################################################################
################################################################################
################################################################################

add_library(gtest
    gtest/src/gtest-all.cc
    gtest/src/gtest_main.cc
)

target_include_directories(gtest
    PUBLIC gtest/include
    PRIVATE gtest
)

add_executable(zlog-test-ram test/test_ram.cc)
#test/test_internal.cc
target_link_libraries(zlog-test-ram
    libzlog
    gtest
    zlog_seqr
    ${Boost_SYSTEM_LIBRARY}
)

if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    setup_target_for_coverage(zlog-test-ram-cov zlog-test-ram coverage)
endif()

################################################################################
################################################################################
################################################################################

if(BUILD_CEPH_BACKEND)

add_library(zstate SHARED zstate/skytype.cc)
target_link_libraries(zstate libzlog zlog_backend_ceph)

add_executable(zlog-test-ceph test/test_ceph.cc)
#test/test_internal.cc
target_link_libraries(zlog-test-ceph
    libzlog
    gtest
    zlog_seqr
    zlog_backend_ceph
    ${Boost_SYSTEM_LIBRARY}
)

add_executable(zlog-seqr seqr-server.cc)
target_link_libraries(zlog-seqr
    libzlog
    zlog_proto
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

add_executable(append-check append-check.cc)
target_link_libraries(append-check
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

add_executable(stream-stress stream-stress.cc)
target_link_libraries(stream-stress
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

add_executable(zlog-seqr-bench zlog-seqr-bench.cc)
target_link_libraries(zlog-seqr-bench
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

add_executable(zlog-bench bench/bench.cc)
target_link_libraries(zlog-bench
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
    atomic
)

add_executable(zlog-bench-ng zlog-bench-ng.cc)
target_link_libraries(zlog-bench-ng
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
    atomic
)

add_executable(zlogtool zlog-tool.cc)
set_target_properties(zlogtool PROPERTIES OUTPUT_NAME "zlog")
target_link_libraries(zlogtool
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

add_executable(zstate-test test/zstate_test.cc)
target_link_libraries(zstate-test
    libzlog
    gtest
    zstate
    zlog_seqr
    zlog_backend_ceph
    ${Boost_SYSTEM_LIBRARY}
)

endif(BUILD_CEPH_BACKEND)
