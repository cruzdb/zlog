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

################################################################################

include_directories(${CMAKE_BINARY_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/src/include)

################################################################################

set(FLATBUFFERS_BUILD_TESTS OFF CACHE "" INTERNAL FORCE)
set(FLATBUFFERS_INSTALL OFF CACHE "" INTERNAL FORCE)
set(FLATBUFFERS_FLATLIB OFF CACHE "" INTERNAL FORCE)
set(FLATBUFFERS_FLATHASH OFF CACHE "" INTERNAL FORCE)
add_subdirectory(flatbuffers EXCLUDE_FROM_ALL)

add_subdirectory(googletest/googlemock)
add_subdirectory(include)
#add_subdirectory(libseq)
add_subdirectory(libzlog)
add_subdirectory(storage)
add_subdirectory(test)

option(WITH_JNI "build with JNI" OFF)
if(WITH_JNI)
  message(STATUS "JNI library is enabled")
  add_subdirectory(java)
else()
  message(STATUS "JNI library is disabled")
endif(WITH_JNI)

# add_executable(zlog-seqr seqr-server.cc)
# target_link_libraries(zlog-seqr
#     libzlog
#     ${Boost_PROGRAM_OPTIONS_LIBRARY}
#     ${Boost_SYSTEM_LIBRARY}
# )
# install(TARGETS zlog-seqr DESTINATION bin)

add_executable(zlog_bench bench.cc)
target_link_libraries(zlog_bench
    libzlog
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)

add_executable(zlog zlog.cc)
target_link_libraries(zlog
    libzlog
    ${Boost_PROGRAM_OPTIONS_LIBRARY}
    ${Boost_SYSTEM_LIBRARY}
)
install(TARGETS zlog DESTINATION bin)
