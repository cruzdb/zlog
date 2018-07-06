include(GNUInstallDirs)

# fixup embedded library paths
SET(CMAKE_SKIP_BUILD_RPATH FALSE)
SET(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE)
SET(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
LIST(FIND CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES
  "${CMAKE_INSTALL_FULL_LIBDIR}" isSystemDir)
IF("${isSystemDir}" STREQUAL "-1")
  SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_FULL_LIBDIR}")
ENDIF("${isSystemDir}" STREQUAL "-1")

set(HDR_HISTOGRAM_BUILD_SHARED OFF CACHE BOOL
  "Disable building hdr_histogram shared library")
set(HDR_HISTOGRAM_BUILD_PROGRAMS OFF CACHE BOOL
  "Disable building hdr_histogram tests and examples")
add_subdirectory(HdrHistogram_c)

################################################################################

include_directories(${CMAKE_BINARY_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/src/include)

################################################################################

add_subdirectory(googletest/googlemock)
add_subdirectory(include)
add_subdirectory(proto)
add_subdirectory(libseq)
add_subdirectory(libzlog)
add_subdirectory(storage)
add_subdirectory(zstate)
add_subdirectory(bench)
add_subdirectory(test)

option(WITH_JNI "build with JNI" OFF)
if(WITH_JNI)
  message(STATUS "JNI library is enabled")
  add_subdirectory(java)
else()
  message(STATUS "JNI library is disabled")
endif(WITH_JNI)

add_executable(zlog-seqr seqr-server.cc)
target_link_libraries(zlog-seqr
    libzlog
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)
install(TARGETS zlog-seqr DESTINATION bin)

if(BUILD_CEPH_BACKEND)

add_executable(zlog_tool zlog_tool.cc)
set_target_properties(zlog_tool PROPERTIES OUTPUT_NAME "zlog")
target_link_libraries(zlog_tool
    libzlog
    zlog_backend_ceph
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

endif(BUILD_CEPH_BACKEND)
