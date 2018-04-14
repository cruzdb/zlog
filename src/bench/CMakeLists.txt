if(BUILD_CEPH_BACKEND)

add_executable(zlog_bench2 bench2.cc)
target_link_libraries(zlog_bench2
    libzlog
    zlog_seqr
    zlog_backend_ceph
    zlog_backend_ram
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
    atomic
)
install(TARGETS zlog_bench2 DESTINATION bin)

endif(BUILD_CEPH_BACKEND)
