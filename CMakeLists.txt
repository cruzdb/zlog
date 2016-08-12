cmake_minimum_required(VERSION 2.8.12)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/modules/")

project(zlog)

# require c++11 (Stolen from Ceph)
include(CheckCXXCompilerFlag)
CHECK_CXX_COMPILER_FLAG("-std=c++11" COMPILER_SUPPORTS_CXX11)
if (COMPILER_SUPPORTS_CXX11)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
else()
  message(FATAL_ERROR "The compiler ${CMAKE_CXX_COMPILER} has no C++11 support.")
endif()

find_package(Boost COMPONENTS system program_options REQUIRED)

find_package(Protobuf REQUIRED)

include_directories(${CMAKE_BINARY_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/src)

if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    include(CodeCoverage)
    SET(CMAKE_CXX_FLAGS "-g -O0 -fprofile-arcs -ftest-coverage")
    SET(CMAKE_C_FLAGS "-g -O0 -fprofile-arcs -ftest-coverage")
endif()

# check for ceph backend dependencies
option(WITH_CEPH_BACKEND "Ceph Backend is here")
if(WITH_CEPH_BACKEND)
    find_package(librados REQUIRED)
    find_package(libcls_zlog_client REQUIRED)
    if(${LIBRADOS_FOUND})
        if(${LIBCLS_ZLOG_CLIENT_FOUND})
            set(BUILD_CEPH_BACKEND ${LIBRADOS_FOUND})
        endif(${LIBCLS_ZLOG_CLIENT_FOUND})
    endif(${LIBRADOS_FOUND})
endif(WITH_CEPH_BACKEND)

add_subdirectory(src)
