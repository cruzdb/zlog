if(BUILD_CEPH_BACKEND)

add_executable(zlog_test_zstate test_zstate.cc)
target_link_libraries(zlog_test_zstate
    libzlog
    gtest_main
    zstate
    zlog_seqr
    zlog_backend_ceph
    ${Boost_SYSTEM_LIBRARY}
)

endif(BUILD_CEPH_BACKEND)
