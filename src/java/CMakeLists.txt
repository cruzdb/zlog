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

set(JAVA_TEST_LIBDIR ${CMAKE_CURRENT_BINARY_DIR}/test-libs)
set(JAVA_TMP_JAR ${JAVA_TEST_LIBDIR}/tmp.jar)
set(JAVA_JUNIT_JAR ${JAVA_TEST_LIBDIR}/junit-4.12.jar)
set(JAVA_HAMCR_JAR ${JAVA_TEST_LIBDIR}/hamcrest-core-1.3.jar)
set(JAVA_ASSERTJ_JAR ${JAVA_TEST_LIBDIR}/assertj-core-1.7.1.jar)
set(JAVA_TESTCLASSPATH "${JAVA_JUNIT_JAR}\;${JAVA_HAMCR_JAR}\;${JAVA_ASSERTJ_JAR}")

if(NOT EXISTS ${JAVA_TEST_LIBDIR})
  file(MAKE_DIRECTORY ${JAVA_TEST_LIBDIR})
endif()

if (DEFINED CUSTOM_REPO_URL)
  set(SEARCH_REPO_URL ${CUSTOM_REPO_URL}/)
  set(CENTRAL_REPO_URL ${CUSTOM_REPO_URL}/)
else ()
  set(SEARCH_REPO_URL "http://search.maven.org/remotecontent?filepath=")
  set(CENTRAL_REPO_URL "http://central.maven.org/maven2/")
endif()

if(NOT EXISTS ${JAVA_JUNIT_JAR})
  message("Downloading ${JAVA_JUNIT_JAR}")
  file(DOWNLOAD ${SEARCH_REPO_URL}junit/junit/4.12/junit-4.12.jar ${JAVA_TMP_JAR} STATUS downloadStatus)
  list(GET downloadStatus 0 error_code)
  if(NOT error_code EQUAL 0)
    message(FATAL_ERROR "Failed downloading ${JAVA_JUNIT_JAR}")
  endif()
  file(RENAME ${JAVA_TMP_JAR} ${JAVA_JUNIT_JAR})
endif()

if(NOT EXISTS ${JAVA_HAMCR_JAR})
  message("Downloading ${JAVA_HAMCR_JAR}")
  file(DOWNLOAD ${SEARCH_REPO_URL}org/hamcrest/hamcrest-core/1.3/hamcrest-core-1.3.jar ${JAVA_TMP_JAR} STATUS downloadStatus)
  list(GET downloadStatus 0 error_code)
  if(NOT error_code EQUAL 0)
    message(FATAL_ERROR "Failed downloading ${JAVA_HAMCR_JAR}")
  endif()
  file(RENAME ${JAVA_TMP_JAR} ${JAVA_HAMCR_JAR})
endif()

if(NOT EXISTS ${JAVA_ASSERTJ_JAR})
  message("Downloading ${JAVA_ASSERTJ_JAR}")
  file(DOWNLOAD ${CENTRAL_REPO_URL}org/assertj/assertj-core/1.7.1/assertj-core-1.7.1.jar ${JAVA_TMP_JAR} STATUS downloadStatus)
  list(GET downloadStatus 0 error_code)
  if(NOT error_code EQUAL 0)
    message(FATAL_ERROR "Failed downloading ${JAVA_ASSERTJ_JAR}")
  endif()
  file(RENAME ${JAVA_TMP_JAR} ${JAVA_ASSERTJ_JAR})
endif()

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

set(CMAKE_JAVA_INCLUDE_PATH ${JAVA_TESTCLASSPATH} ${zlog_jar_path})
set(java_test_srcs
  src/test/java/com/cruzdb/AllTests.java
  src/test/java/com/cruzdb/LogTest.java)
add_jar(zlog-test ${java_test_srcs})
add_dependencies(zlog-test zlog_jar)
install_jar(zlog-test share/java)

create_javadoc(zlog
  PACKAGES com.cruzdb
  SOURCEPATH ${CMAKE_CURRENT_SOURCE_DIR}/src/main/java
  WINDOWTITLE "ZLogJava"
  DOCTITLE "<h1>ZLog</h1>"
  AUTHOR FALSE
  USE TRUE
  VERSION FALSE)
