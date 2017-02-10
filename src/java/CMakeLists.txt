if(BUILD_CEPH_BACKEND)

find_package(Java COMPONENTS Development REQUIRED)
find_package(JNI REQUIRED)
include(UseJava)

add_subdirectory(native)

set(java_srcs
  src/main/java/com/cruzdb/FilledException.java
  src/main/java/com/cruzdb/Log.java
  src/main/java/com/cruzdb/LogException.java
  src/main/java/com/cruzdb/NativeLibraryLoader.java
  src/main/java/com/cruzdb/NotWrittenException.java
  src/main/java/com/cruzdb/ReadOnlyException.java
  src/main/java/com/cruzdb/ZObject.java)

set(CMAKE_JAVA_COMPILE_FLAGS "-source" "1.7" "-target" "1.7" "-Xlint:-options")
add_jar(zlog_jar SOURCES ${java_srcs} OUTPUT_NAME zlog)
install_jar(zlog_jar share/java)

set(java_classes
  com.cruzdb.FilledException
  com.cruzdb.Log
  com.cruzdb.LogException
  com.cruzdb.NativeLibraryLoader
  com.cruzdb.NotWrittenException
  com.cruzdb.ZObject)

create_javah(TARGET jni_headers
  CLASSES ${java_classes}
  CLASSPATH zlog_jar
  OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/native)

endif(BUILD_CEPH_BACKEND)
