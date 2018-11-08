#!/bin/bash
set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

# setup temp dirs
BUILD_DIR=$(mktemp -d)
DOCS_DIR=$(mktemp -d)
INSTALL_DIR=$(mktemp -d)
trap "rm -rf ${BUILD_DIR} \
  ${DOCS_DIR} ${INSTALL_DIR}" EXIT

# build documentation
${ZLOG_DIR}/doc/build.sh ${DOCS_DIR}
test -r ${DOCS_DIR}/output/html/index.html

# build and install zlog
CMAKE_BUILD_TYPE=Debug
if [ "${RUN_COVERAGE}" == 1 ]; then
  CMAKE_BUILD_TYPE=Coverage
fi

CMAKE_FLAGS="-DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} \
             -DCMAKE_INSTALL_PREFIX=${INSTALL_DIR}"

# TODO reenable java. javah not in newer jdks?
JNI="ON"
if ! [ -x "$(command -v javah)" ]; then
  JNI="OFF"
fi

# TODO: renable ceph support
# CMAKE_FLAGS="${CMAKE_FLAGS} -DWITH_CEPH=ON -DWITH_JNI=${JNI}"
if [[ "$OSTYPE" != "darwin"* ]]; then
  CMAKE_FLAGS="${CMAKE_FLAGS} -DWITH_JNI=${JNI}"
fi

pushd ${BUILD_DIR}
cmake ${CMAKE_FLAGS} ${ZLOG_DIR}
make -j$(nproc) VERBOSE=1
make install
popd

PATH=${INSTALL_DIR}/bin:$PATH

# list of tests to run
tests="zlog_test_backend_lmdb zlog_test_backend_ram"

# run ceph backend tests
export CEPH_CONF=/tmp/micro-osd/ceph.conf
if [ -e ${CEPH_CONF} ]; then
  ceph --version || true
  ceph status || true

  # ceph tests
  tests="${tests} zlog_test_cls_zlog"
  tests="${tests} zlog_test_backend_ceph"
fi

# start the sequencer
#zlog-seqr --port 5678 --streams --daemon

for test_runner in $tests; do
  ${test_runner}
  # TODO: reenable coverage
  if [ "${RUN_COVERAGE}" == 1 ]; then
    pushd ${BUILD_DIR}
    make ${test_runner}_coverage || (popd && continue)
    rm -rf coverage*
    lcov --directory . --capture --output-file coverage.info
    lcov --remove coverage.info '/usr/*' '*/googletest/*' '*.pb.cc' '*.pb.h' --output-file coverage2.info
    bash <(curl -s https://codecov.io/bash) -R ${ZLOG_DIR} -f coverage2.info || \
      echo "Codecov did not collect coverage reports"
    popd
  fi
done

if [[ "$OSTYPE" != "darwin"* && "$JNI" == "ON" ]]; then
  pushd ${BUILD_DIR}/src/java

  export LD_LIBRARY_PATH=${INSTALL_DIR}/lib:${INSTALL_DIR}/lib64:${INSTALL_DIR}/lib/x86_64-linux-gnu:/usr/lib/x86_64-linux-gnu:$LD_LIBRARY_PATH

  # i'm giving up for the time being on how to fix a dynamic library loading
  # issue that is only showing up on debian jessie. see issue #143
  
  if [[ ${OS_ID} == "Debian" && ${OS_CODE} == "jessie" ]]; then
    export LD_LIBRARY_PATH=/usr/lib/jvm/java-7-openjdk-amd64/jre/lib/amd64/xawt/:$LD_LIBRARY_PATH
  fi

  export CP=${INSTALL_DIR}/share/java/zlog.jar
  export CP=${CP}:${INSTALL_DIR}/share/java/zlog-test.jar
  export CP=${CP}:${BUILD_DIR}/src/java/test-libs/junit-4.12.jar
  export CP=${CP}:${BUILD_DIR}/src/java/test-libs/hamcrest-core-1.3.jar
  export CP=${CP}:${BUILD_DIR}/src/java/test-libs/assertj-core-1.7.1.jar

  mkdir db
  java -cp $CP org.junit.runner.JUnitCore org.cruzdb.zlog.AllTests

  popd
fi
