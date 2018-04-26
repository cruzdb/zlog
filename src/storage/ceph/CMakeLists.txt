if(BUILD_CEPH_BACKEND)
PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS cls_zlog.proto)
add_library(zlog_ceph_proto SHARED ${PROTO_SRCS} ${PROTO_HDRS})
target_link_libraries(zlog_ceph_proto
    ${PROTOBUF_LIBRARIES}
)
target_include_directories(zlog_ceph_proto
    PUBLIC ${PROTOBUF_INCLUDE_DIR}
)
install(TARGETS zlog_ceph_proto DESTINATION ${CMAKE_INSTALL_LIBDIR})

add_library(cls_zlog_client SHARED cls_zlog_client.cc)
target_link_libraries(cls_zlog_client
    zlog_ceph_proto
    rados)
target_include_directories(cls_zlog_client
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
)
install(TARGETS cls_zlog_client DESTINATION ${CMAKE_INSTALL_LIBDIR})

add_library(zlog_backend_ceph SHARED ceph.cc)
target_link_libraries(zlog_backend_ceph
    cls_zlog_client
    rados)
target_include_directories(zlog_backend_ceph
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
)
install(TARGETS zlog_backend_ceph DESTINATION ${CMAKE_INSTALL_LIBDIR})

add_executable(zlog_test_cls_zlog
  test_cls_zlog.cc
  ../../port/stack_trace.cc)
target_link_libraries(zlog_test_cls_zlog
    cls_zlog_client
    rados
    gtest)
target_include_directories(zlog_test_cls_zlog
    PUBLIC ${LIBRADOS_INCLUDE_DIRS}
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

PROTOBUF_GENERATE_CPP(BENCH_PROTO_SRCS BENCH_PROTO_HDRS adapter_test.proto)
add_executable(adapter_bench adapter_bench.cc ${BENCH_PROTO_SRCS} ${BENCH_PROTO_HDRS})
target_link_libraries(adapter_bench rados ${PROTOBUF_LIBRARIES})
target_include_directories(adapter_bench PUBLIC ${PROTOBUF_INCLUDE_DIR})

endif(BUILD_CEPH_BACKEND)

if(HAVE_RADOS_OBJECT_CLASS_H)
  add_library(cls_zlog SHARED cls_zlog.cc ${PROTO_SRCS} ${PROTO_HDRS})
  target_link_libraries(cls_zlog ${PROTOBUF_LIBRARIES})
  target_include_directories(cls_zlog
    PRIVATE ${CMAKE_SOURCE_DIR}/src/CRoaringUnityBuild)
  set_target_properties(cls_zlog PROPERTIES
    VERSION "1.0.0"
    SOVERSION "1")
  install(TARGETS cls_zlog DESTINATION ${CMAKE_INSTALL_LIBDIR}/rados-classes)
endif(HAVE_RADOS_OBJECT_CLASS_H)
