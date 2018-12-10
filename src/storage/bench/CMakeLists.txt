add_executable(zlog_backend_bench backend_bench.cc)
target_link_libraries(zlog_backend_bench
    libzlog
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)
