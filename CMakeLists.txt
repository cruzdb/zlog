cmake_minimum_required(VERSION 2.8.12)
project(zlog)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake/modules/")

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if(APPLE)
  cmake_policy(SET CMP0042 NEW)
endif()

# add os macros
if(CMAKE_SYSTEM_NAME MATCHES "Cygwin")
  add_definitions(-fno-builtin-memcmp -DCYGWIN)
elseif(CMAKE_SYSTEM_NAME MATCHES "Darwin")
  add_definitions(-DOS_MACOSX)
  if(CMAKE_SYSTEM_PROCESSOR MATCHES arm)
    add_definitions(-DIOS_CROSS_COMPILE -DROCKSDB_LITE)
    # no debug info for IOS, that will make our library big
    add_definitions(-DNDEBUG)
  endif()
elseif(CMAKE_SYSTEM_NAME MATCHES "Linux")
  add_definitions(-DOS_LINUX)
elseif(CMAKE_SYSTEM_NAME MATCHES "SunOS")
  add_definitions(-DOS_SOLARIS)
elseif(CMAKE_SYSTEM_NAME MATCHES "FreeBSD")
  add_definitions(-DOS_FREEBSD)
elseif(CMAKE_SYSTEM_NAME MATCHES "NetBSD")
  add_definitions(-DOS_NETBSD)
elseif(CMAKE_SYSTEM_NAME MATCHES "OpenBSD")
  add_definitions(-DOS_OPENBSD)
elseif(CMAKE_SYSTEM_NAME MATCHES "DragonFly")
  add_definitions(-DOS_DRAGONFLYBSD)
elseif(CMAKE_SYSTEM_NAME MATCHES "Android")
  add_definitions(-DOS_ANDROID)
elseif(CMAKE_SYSTEM_NAME MATCHES "Windows")
  add_definitions(-DWIN32 -DOS_WIN -D_MBCS -DWIN64 -DNOMINMAX)
  if(MINGW)
    add_definitions(-D_WIN32_WINNT=_WIN32_WINNT_VISTA)
  endif()
endif()

# put all the libs and binaries in one place
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Werror -Wall -g")
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Werror -Wall -g")

if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
    include(CodeCoverage)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -fprofile-arcs -ftest-coverage")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -O0 -fprofile-arcs -ftest-coverage")
endif()

# require c++11 (Stolen from Ceph)
include(CheckCXXCompilerFlag)
CHECK_CXX_COMPILER_FLAG("-std=c++11" COMPILER_SUPPORTS_CXX11)
if (COMPILER_SUPPORTS_CXX11)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
else()
  message(FATAL_ERROR "The compiler ${CMAKE_CXX_COMPILER} has no C++11 support.")
endif()

# check dependencies
find_package(Boost COMPONENTS system program_options REQUIRED)
find_package(LMDB REQUIRED)

include(CheckIncludeFile)
CHECK_INCLUDE_FILE(rados/objclass.h HAVE_RADOS_OBJECT_CLASS_H)

find_package(Protobuf REQUIRED)
if(NOT PROTOBUF_PROTOC_EXECUTABLE)
  message(FATAL_ERROR "cannot find protobuf compiler")
endif()

find_package(librados)
option(WITH_CEPH "Build Ceph backend" OFF)
if(${LIBRADOS_FOUND})
  message(STATUS "Building Ceph backend ${LIBRADOS_LIBRARIES}")
  set(BUILD_CEPH_BACKEND TRUE)
elseif(WITH_CEPH)
  message(FATAL_ERROR "Cannot find librados")
endif()

option(WITH_CACHING "Enable caching" OFF)
if(WITH_CACHING)
  message(STATUS "Caching is enabled")
  add_definitions(-DWITH_CACHE -DWITH_STATS)
else()
  message(STATUS "Caching is disabled")
endif()

find_package(Backtrace)

add_subdirectory(src)
