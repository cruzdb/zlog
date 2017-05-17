add_library(zlogjni SHARED
  zlogjni.cc
  portal.h)
set_target_properties(zlogjni PROPERTIES
  VERSION 1.0.0
  SOVERSION 1)

set(add_libs libzlog zlog_seqr ${JNI_LIBRARIES})

if(BUILD_CEPH_BACKEND)
  target_compile_definitions(zlogjni PRIVATE -DWITH_RADOS)
  list(APPEND add_libs zlog_backend_ceph)
endif(BUILD_CEPH_BACKEND)

add_dependencies(zlogjni jni_headers)
include_directories(${JNI_INCLUDE_DIRS} ${CMAKE_CURRENT_BINARY_DIR})
target_link_libraries(zlogjni LINK_PRIVATE ${add_libs})
install(TARGETS zlogjni DESTINATION lib)
