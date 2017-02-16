cmake_minimum_required(VERSION 2.8.12)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/modules/")

project(zlog)

if(APPLE)
  cmake_policy(SET CMP0042 NEW)
endif()

if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    include(CodeCoverage)
    SET(CMAKE_CXX_FLAGS "-g -O0 -fprofile-arcs -ftest-coverage")
    SET(CMAKE_C_FLAGS "-g -O0 -fprofile-arcs -ftest-coverage")
endif()

# require c++11 (Stolen from Ceph)
include(CheckCXXCompilerFlag)
CHECK_CXX_COMPILER_FLAG("-std=c++11" COMPILER_SUPPORTS_CXX11)
if (COMPILER_SUPPORTS_CXX11)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
else()
  message(FATAL_ERROR "The compiler ${CMAKE_CXX_COMPILER} has no C++11 support.")
endif()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Werror -Wall")
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Werror -Wall")

find_package(Boost COMPONENTS system program_options REQUIRED)
find_package(Protobuf REQUIRED)

# check for ceph backend dependencies. the way this is setup is that unless
# the ceph backend is disabled, it will be built if the dependencies are
# found. TODO: it would be nice to distinguish between default-ON and user
# requested ON so that we can abort/fail if the dependencies are not found
# and the user explicitly requested the ceph backend.
option(WITH_CEPH_BACKEND "Ceph Backend is here" ON)
if(WITH_CEPH_BACKEND)
    find_package(librados)
    find_package(libcls_zlog_client)
    if(${LIBRADOS_FOUND})
        if(${LIBCLS_ZLOG_CLIENT_FOUND})
            set(BUILD_CEPH_BACKEND ${LIBRADOS_FOUND})
        endif(${LIBCLS_ZLOG_CLIENT_FOUND})
    endif(${LIBRADOS_FOUND})
endif(WITH_CEPH_BACKEND)

add_subdirectory(src)
