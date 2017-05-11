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

get_property(zlog_jar_path TARGET zlog_jar PROPERTY JAR_FILE)
set(java_h native/com_cruzdb_Log.h)
add_custom_command(
  OUTPUT ${java_h}
  COMMAND ${Java_JAVAH_EXECUTABLE} -classpath ${zlog_jar_path} -jni -o ${CMAKE_CURRENT_BINARY_DIR}/${java_h} com.cruzdb.Log)
add_custom_target(
  jni_headers
  DEPENDS ${java_h})
add_dependencies(jni_headers zlog_jar)

find_jar(JUNIT_JAR
  NAMES junit junit4
  PATHS "/usr/share/java")
if(JUNIT_JAR)
  set(CMAKE_JAVA_INCLUDE_PATH ${JUNIT_JAR} ${zlog_jar_path})
  set(java_test_srcs
    src/test/java/com/cruzdb/AllTests.java
    src/test/java/com/cruzdb/LogTest.java)
  add_jar(zlog-test ${java_test_srcs})
  add_dependencies(zlog-test zlog_jar)
  install_jar(zlog-test share/java)
endif(JUNIT_JAR)
