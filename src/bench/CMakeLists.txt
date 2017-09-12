if(BUILD_CEPH_BACKEND)

add_executable(zlog_bench bench.cc)
target_link_libraries(zlog_bench
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
    atomic
)
install(TARGETS zlog_bench DESTINATION bin)

endif(BUILD_CEPH_BACKEND)
