build_flatbuffers("cls_zlog.fbs" "" cls_zlog_schemas "" "${CMAKE_CURRENT_BINARY_DIR}" "" "")

if(BUILD_CEPH_BACKEND)
add_library(cls_zlog_client OBJECT cls_zlog_client.cc)
target_include_directories(cls_zlog_client
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
    PUBLIC ${PROJECT_SOURCE_DIR}/src/flatbuffers/include
)
set_property(TARGET cls_zlog_client PROPERTY POSITION_INDEPENDENT_CODE ON)
add_dependencies(cls_zlog_client cls_zlog_schemas)

add_library(zlog_backend_ceph SHARED
  ceph.cc
  $<TARGET_OBJECTS:cls_zlog_client>)
target_link_libraries(zlog_backend_ceph rados)
target_include_directories(zlog_backend_ceph
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
    PUBLIC ${PROJECT_SOURCE_DIR}/src/flatbuffers/include
)
set_target_properties(zlog_backend_ceph PROPERTIES
  OUTPUT_NAME zlog_backend_ceph
  VERSION 1.0.0
  SOVERSION 1)
install(TARGETS zlog_backend_ceph DESTINATION ${CMAKE_INSTALL_LIBDIR})

add_executable(zlog_test_cls_zlog
  test_cls_zlog.cc
  ../../port/stack_trace.cc
  $<TARGET_OBJECTS:cls_zlog_client>)
target_link_libraries(zlog_test_cls_zlog
    rados
    gtest)
target_include_directories(zlog_test_cls_zlog
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
    PUBLIC ${PROJECT_SOURCE_DIR}/src/flatbuffers/include
)
install(TARGETS zlog_test_cls_zlog DESTINATION bin)
if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
  setup_target_for_coverage(zlog_test_cls_zlog_coverage zlog_test_cls_zlog coverage)
endif()

add_executable(zlog_test_backend_ceph
  test_backend_ceph.cc
  $<TARGET_OBJECTS:test_backend>
  $<TARGET_OBJECTS:test_libzlog>)
target_link_libraries(zlog_test_backend_ceph
  ${Boost_SYSTEM_LIBRARY}
  zlog_backend_ceph
  rados
  libzlog
  gtest)
install(TARGETS zlog_test_backend_ceph DESTINATION bin)
if (CMAKE_BUILD_TYPE STREQUAL "Coverage")
  setup_target_for_coverage(zlog_test_backend_ceph_coverage zlog_test_backend_ceph coverage)
endif()
endif(BUILD_CEPH_BACKEND)

if(HAVE_RADOS_OBJECT_CLASS_H)
  add_library(cls_zlog SHARED cls_zlog.cc)
  add_dependencies(cls_zlog cls_zlog_schemas)
  target_include_directories(cls_zlog
    PRIVATE ${CMAKE_SOURCE_DIR}/src/CRoaringUnityBuild
    PUBLIC ${PROJECT_SOURCE_DIR}/src/flatbuffers/include)
  set_target_properties(cls_zlog PROPERTIES
    VERSION "1.0.0"
    SOVERSION "1")
  install(TARGETS cls_zlog DESTINATION ${CMAKE_INSTALL_LIBDIR}/rados-classes)
endif(HAVE_RADOS_OBJECT_CLASS_H)
