add_library(zlogjni SHARED
  zlogjni.cc
  portal.h)
set_target_properties(zlogjni PROPERTIES
  VERSION 1.0.0
  SOVERSION 1)
add_dependencies(zlogjni jni_headers)
include_directories(${JNI_INCLUDE_DIRS} ${CMAKE_CURRENT_BINARY_DIR})
target_link_libraries(zlogjni LINK_PRIVATE libzlog zlog_seqr zlog_backend_ceph ${JNI_LIBRARIES})
install(TARGETS zlogjni DESTINATION lib)
