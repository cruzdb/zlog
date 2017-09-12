include_directories(${CMAKE_BINARY_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/src/include)
include_directories(${CMAKE_SOURCE_DIR}/src/spdlog/include)
include_directories(${CMAKE_SOURCE_DIR}/src/rapidjson/include)

################################################################################

add_subdirectory(googletest/googlemock)
add_subdirectory(include)
add_subdirectory(proto)
add_subdirectory(libseq)
add_subdirectory(libzlog)
add_subdirectory(storage)
add_subdirectory(kvstore)
add_subdirectory(zstate)
add_subdirectory(tools)
add_subdirectory(bench)

option(WITH_JNI "build with JNI" OFF)
if(WITH_JNI)
  message(STATUS "JNI library is enabled")
  add_subdirectory(java)
else()
  message(STATUS "JNI library is disabled")
endif(WITH_JNI)

################################################################################

if(BUILD_CEPH_BACKEND)

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

add_executable(zlog_tool zlog_tool.cc)
set_target_properties(zlog_tool PROPERTIES OUTPUT_NAME "zlog")
target_link_libraries(zlog_tool
    libzlog
    zlog_seqr
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

endif(BUILD_CEPH_BACKEND)
