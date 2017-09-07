include_directories(${CMAKE_BINARY_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/src/include)
include_directories("${CMAKE_SOURCE_DIR}/src/spdlog/include")

add_subdirectory(proto)
add_subdirectory(libseq)
add_subdirectory(libzlog)
add_subdirectory(kvstore)
add_subdirectory(include)
add_subdirectory(googletest/googlemock)
add_subdirectory(test)

option(WITH_JNI "build with JNI" OFF)
if(WITH_JNI)
  message(STATUS "JNI library is enabled")
  add_subdirectory(java)
else()
  message(STATUS "JNI library is disabled")
endif(WITH_JNI)

include_directories(SYSTEM "${CMAKE_SOURCE_DIR}/src/rapidjson/include")
add_subdirectory(tools)

################################################################################
################################################################################
################################################################################

if(BUILD_CEPH_BACKEND)

add_library(zstate SHARED zstate/skytype.cc)
target_link_libraries(zstate libzlog zlog_backend_ceph)

add_executable(zlog-seqr seqr-server.cc)
target_link_libraries(zlog-seqr
    libzlog
    zlog_proto
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)
install(TARGETS zlog-seqr DESTINATION bin)

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
install(TARGETS zlog-seqr-bench DESTINATION bin)

add_executable(zlog-bench bench/bench.cc)
target_link_libraries(zlog-bench
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
    atomic
)
install(TARGETS zlog-bench DESTINATION bin)

add_executable(zlog-bench-ng zlog-bench-ng.cc)
target_link_libraries(zlog-bench-ng
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
    atomic
)
install(TARGETS zlog-bench-ng DESTINATION bin)

add_executable(zlogtool zlog-tool.cc)
set_target_properties(zlogtool PROPERTIES OUTPUT_NAME "zlog")
target_link_libraries(zlogtool
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

endif(BUILD_CEPH_BACKEND)
