if(BUILD_CEPH_BACKEND)

add_executable(zlog_cache_bench cache_bench.cc)
target_link_libraries(zlog_cache_bench
    libzlog
    zlog_seqr
    zlog_backend_ceph
    zlog_backend_lmdb
    zlog_backend_ram
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
    atomic
    hdr_histogram_static
)
install(TARGETS zlog_cache_bench DESTINATION bin)

endif(BUILD_CEPH_BACKEND)
