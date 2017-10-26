find_package(Java COMPONENTS Development REQUIRED)
find_package(JNI REQUIRED)
include(UseJava)

add_subdirectory(native)

set(java_srcs
  src/main/java/org/cruzdb/zlog/FilledException.java
  src/main/java/org/cruzdb/zlog/Log.java
  src/main/java/org/cruzdb/zlog/LogException.java
  src/main/java/org/cruzdb/zlog/NativeLibraryLoader.java
  src/main/java/org/cruzdb/zlog/NotWrittenException.java
  src/main/java/org/cruzdb/zlog/ReadOnlyException.java
  src/main/java/org/cruzdb/zlog/ZObject.java)

set(CMAKE_JAVA_COMPILE_FLAGS "-source" "1.7" "-target" "1.7" "-Xlint:-options")
add_jar(zlog_jar SOURCES ${java_srcs} OUTPUT_NAME zlog)
install_jar(zlog_jar share/java)

set(java_classes
  org.cruzdb.zlog.FilledException
  org.cruzdb.zlog.Log
  org.cruzdb.zlog.LogException
  org.cruzdb.zlog.NativeLibraryLoader
  org.cruzdb.zlog.NotWrittenException
  org.cruzdb.zlog.ZObject)

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
set(java_h native/org_cruzdb_zlog_Log.h)
add_custom_command(
  OUTPUT ${java_h}
  DEPENDS ${java_srcs}
  COMMAND ${Java_JAVAH_EXECUTABLE} -classpath ${zlog_jar_path}
    -jni -o ${CMAKE_CURRENT_BINARY_DIR}/${java_h} org.cruzdb.zlog.Log)

add_custom_target(
  jni_headers
  DEPENDS ${java_h})
add_dependencies(jni_headers zlog_jar)

set(CMAKE_JAVA_INCLUDE_PATH ${JAVA_TESTCLASSPATH} ${zlog_jar_path})
set(java_test_srcs
  src/test/java/org/cruzdb/zlog/AllTests.java
  src/test/java/org/cruzdb/zlog/LogTest.java)
add_jar(zlog-test ${java_test_srcs})
add_dependencies(zlog-test zlog_jar)
install_jar(zlog-test share/java)

create_javadoc(zlog
  PACKAGES org.cruzdb.zlog
  SOURCEPATH ${CMAKE_CURRENT_SOURCE_DIR}/src/main/java
  WINDOWTITLE "ZLogJava"
  DOCTITLE "<h1>ZLog</h1>"
  AUTHOR FALSE
  USE TRUE
  VERSION FALSE)
