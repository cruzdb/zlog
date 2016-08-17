add_executable(db_test db_test.cc)
target_link_libraries(db_test libzlog zlog_seqr gtest_main libkvstore)
if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    setup_target_for_coverage(dbtest2-cov db_test coverage)
endif()


add_executable(zlog-test-ram test_ram.cc)
#test/test_internal.cc
target_link_libraries(zlog-test-ram
    libzlog gtest_main zlog_seqr ${Boost_SYSTEM_LIBRARY}
)
if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    setup_target_for_coverage(zlog-test-ram-cov zlog-test-ram coverage)
endif()

if(BUILD_CEPH_BACKEND)

add_executable(zlog-test-ceph test_ceph.cc)
#test/test_internal.cc
target_link_libraries(zlog-test-ceph
    libzlog
    gtest_main
    zlog_seqr
    zlog_backend_ceph
    ${Boost_SYSTEM_LIBRARY}
)

add_executable(zstate-test zstate_test.cc)
target_link_libraries(zstate-test
    libzlog
    gtest_main
    zstate
    zlog_seqr
    zlog_backend_ceph
    ${Boost_SYSTEM_LIBRARY}
)
endif(BUILD_CEPH_BACKEND)
