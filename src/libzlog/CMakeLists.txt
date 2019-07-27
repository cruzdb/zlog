build_flatbuffers("zlog.fbs" "" zlog_schemas "" "${CMAKE_CURRENT_BINARY_DIR}" "" "")

set(libzlog_sources
  log_impl.cc
  view_manager.cc
  capi.cc
  log.cc
  backend.cc
  cache.cc
  stripe.cc
  object_map.cc
  view.cc
  sequencer.cc
  view_reader.cc
  ../eviction/lru.cc
  ../eviction/arc.cc
  ../port/stack_trace.cc
  ../port/port_posix.cc
  ../util/random.cc
  ../util/thread_local.cc
  ../monitoring/statistics.cc
  ../monitoring/histogram.cc
  ../util/mempool.cc)

add_definitions("-DZLOG_LIBDIR=\"${CMAKE_INSTALL_FULL_LIBDIR}\"")
add_definitions("-DCMAKE_SHARED_LIBRARY_SUFFIX=\"${CMAKE_SHARED_LIBRARY_SUFFIX}\"")
add_definitions("-DCMAKE_SHARED_LIBRARY_PREFIX=\"${CMAKE_SHARED_LIBRARY_PREFIX}\"")

add_library(libzlog SHARED ${libzlog_sources})
add_dependencies(libzlog zlog_schemas)

target_include_directories(libzlog
    PUBLIC ${PROJECT_SOURCE_DIR}/src/flatbuffers/include
    PUBLIC ${PROJECT_SOURCE_DIR}/src/json/single_include
)

target_link_libraries(libzlog
    dl
    pthread
    ${Boost_SYSTEM_LIBRARY}
    ${Backtrace_LIBRARIES}
)

set_target_properties(libzlog PROPERTIES
  OUTPUT_NAME zlog
  VERSION 1.0.0
  SOVERSION 1)

install(TARGETS libzlog LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})

add_library(test_libzlog OBJECT
    test_libzlog.cc
    stripe_test.cc
    object_map_test.cc
    view_test.cc
    log_backend_test.cc
    view_reader_test.cc)
target_include_directories(test_libzlog
  PUBLIC ${Boost_INCLUDE_DIRS}
  # TODO: flatbuffers should be included from libzlog. if we can fix that, we
  # also want that to only apply to internal binaries.
  PUBLIC ${PROJECT_SOURCE_DIR}/src/flatbuffers/include
  PUBLIC ${PROJECT_SOURCE_DIR}/src/json/single_include
  PRIVATE $<TARGET_PROPERTY:gtest,INTERFACE_INCLUDE_DIRECTORIES>)

# needs the generated flatbuffers headers. but this object file isn't linked
# against libzlog (that is done by the per-backend targets) so it doesn't get
# this dependency automatically.
add_dependencies(test_libzlog zlog_schemas)
