add_executable(zlog-db-test db_test.cc)
target_link_libraries(zlog-db-test libzlog zlog_seqr gtest_main libkvstore)
if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    setup_target_for_coverage(zlog-db-test-cov zlog-db-test coverage)
endif()
install(TARGETS zlog-db-test DESTINATION bin)

add_executable(zlog-test-ram test_ram.cc)
#test/test_internal.cc
target_link_libraries(zlog-test-ram
    libzlog gtest_main zlog_seqr ${Boost_SYSTEM_LIBRARY}
)
if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    setup_target_for_coverage(zlog-test-ram-cov zlog-test-ram coverage)
endif()
install(TARGETS zlog-test-ram DESTINATION bin)

add_executable(zlog-test-lmdb test_lmdb.cc)
#test/test_internal.cc
target_link_libraries(zlog-test-lmdb
    libzlog gtest_main zlog_seqr ${Boost_SYSTEM_LIBRARY} ${LMDB_LIBRARIES}
)
if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    setup_target_for_coverage(zlog-test-lmdb-cov zlog-test-lmdb coverage)
endif()
install(TARGETS zlog-test-lmdb DESTINATION bin)

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
install(TARGETS zlog-test-ceph DESTINATION bin)

if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    setup_target_for_coverage(zlog-test-ceph-cov zlog-test-ceph coverage)
endif()

add_executable(zstate-test zstate_test.cc)
target_link_libraries(zstate-test
    libzlog
    gtest_main
    zstate
    zlog_seqr
    zlog_backend_ceph
    ${Boost_SYSTEM_LIBRARY}
)

add_executable(zlog-test-cls-zlog
    test_cls_zlog.cc)
target_link_libraries(zlog-test-cls-zlog
    cls_zlog_client
    ${LIBRADOS_LIBRARIES}
    gtest_main)
target_include_directories(zlog-test-cls-zlog
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
)
install(TARGETS zlog-test-cls-zlog DESTINATION bin)

endif(BUILD_CEPH_BACKEND)
