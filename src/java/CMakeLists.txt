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
  src/main/java/com/cruzdb/ZObject.java
  src/main/java/com/cruzdb/DB.java
  src/main/java/com/cruzdb/CruzIterator.java
  src/main/java/com/cruzdb/Transaction.java)

set(CMAKE_JAVA_COMPILE_FLAGS "-source" "1.7" "-target" "1.7" "-Xlint:-options")
add_jar(zlog_jar SOURCES ${java_srcs} OUTPUT_NAME zlog)
install_jar(zlog_jar share/java)

set(java_classes
  com.cruzdb.FilledException
  com.cruzdb.Log
  com.cruzdb.LogException
  com.cruzdb.NativeLibraryLoader
  com.cruzdb.NotWrittenException
  com.cruzdb.ZObject
  com.cruzdb.DB
  com.cruzdb.CruzIterator
  com.cruzdb.Transaction)

get_property(zlog_jar_path TARGET zlog_jar PROPERTY JAR_FILE)

# TODO:
#   https://cmake.org/Wiki/CMake_FAQ#How_can_I_generate_a_source_file_during_the_build.3F
#
set(java_h native/com_cruzdb_Log.h)
add_custom_command(
  OUTPUT ${java_h}
  DEPENDS ${java_srcs}
  COMMAND ${Java_JAVAH_EXECUTABLE} -classpath ${zlog_jar_path} -jni -o ${CMAKE_CURRENT_BINARY_DIR}/${java_h} com.cruzdb.Log)

set(java_db_h native/com_cruzdb_DB.h)
add_custom_command(
  OUTPUT ${java_db_h}
  DEPENDS ${java_srcs}
  COMMAND ${Java_JAVAH_EXECUTABLE} -classpath ${zlog_jar_path} -jni -o ${CMAKE_CURRENT_BINARY_DIR}/${java_db_h} com.cruzdb.DB)

set(java_it_h native/com_cruzdb_CruzIterator.h)
add_custom_command(
  OUTPUT ${java_it_h}
  DEPENDS ${java_srcs}
  COMMAND ${Java_JAVAH_EXECUTABLE} -classpath ${zlog_jar_path} -jni -o ${CMAKE_CURRENT_BINARY_DIR}/${java_it_h} com.cruzdb.CruzIterator)

set(java_txn_h native/com_cruzdb_Transaction.h)
add_custom_command(
  OUTPUT ${java_txn_h}
  DEPENDS ${java_srcs}
  COMMAND ${Java_JAVAH_EXECUTABLE} -classpath ${zlog_jar_path} -jni -o ${CMAKE_CURRENT_BINARY_DIR}/${java_txn_h} com.cruzdb.Transaction)

add_custom_target(
  jni_headers
  DEPENDS ${java_h} ${java_db_h} ${java_it_h} ${java_txn_h})
add_dependencies(jni_headers zlog_jar)

find_jar(JUNIT_JAR
  NAMES junit junit4
  PATHS "/usr/share/java")
find_jar(ASSERTJ_JAR
  NAMES assertj-core
  PATHS "/usr/share/java/assertj-core")
if(JUNIT_JAR)
if(ASSERTJ_JAR)
  set(CMAKE_JAVA_INCLUDE_PATH ${JUNIT_JAR} ${ASSERTJ_JAR} ${zlog_jar_path})
  set(java_test_srcs
    src/test/java/com/cruzdb/AllTests.java
    src/test/java/com/cruzdb/LogTest.java)
  add_jar(zlog-test ${java_test_srcs})
  add_dependencies(zlog-test zlog_jar)
  install_jar(zlog-test share/java)
endif(ASSERTJ_JAR)
endif(JUNIT_JAR)
