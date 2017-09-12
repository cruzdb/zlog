#!/bin/bash

set -e

COVERAGE_ENV=""
if [ "${RUN_COVERAGE}" == 1 ]; then
  COVERAGE_ENV="-e `bash <(curl -s https://codecov.io/env)`"
fi

echo $COVERAGE_ENV
env

if [ ! -z ${DOCKER_IMAGE+x} ]; then
  docker run --rm -v ${TRAVIS_BUILD_DIR}:/zlog:ro -w /zlog \
    ${COVERAGE_ENV} ${DOCKER_IMAGE} \
    /bin/bash -c "env && ./install-deps.sh && ./ci/install-ceph.sh && ./ci/run.sh"
else
  ${TRAVIS_BUILD_DIR}/install-deps.sh
  ${TRAVIS_BUILD_DIR}/ci/install-ceph.sh
  ${TRAVIS_BUILD_DIR}/ci/run.sh
fi

#if [[ "$OSTYPE" == "linux"* ]]; then
#  export EXTRA_CMAKE_ARGS="-DWITH_CEPH=ON"
#  export CEPH_CONF="/tmp/micro-osd/ceph.conf"
#else
#  export EXTRA_CMAKE_ARGS=""
#  export CEPH_CONF=""
#fi
#
#if [ ! -z ${DOCKER_IMAGE+x} ]; then
#  ci_env=""
#  if [ "${RUN_COVERAGE}" == 1 ]; then
#    ci_env=`bash <(curl -s https://codecov.io/env)`
#  fi
#  docker run --net=host --rm -v ${TRAVIS_BUILD_DIR}:/zlog -w="/zlog" \
#    -v /tmp/micro-osd/:/tmp/micro-osd \
#    $ci_env -e RUN_COVERAGE=${RUN_COVERAGE} \
#    ${DOCKER_IMAGE} /bin/bash -c "./install-deps.sh && ./ci/install-ceph.sh && CEPH_CONF=${CEPH_CONF} EXTRA_CMAKE_ARGS=${EXTRA_CMAKE_ARGS} ./ci/run.sh"
#else
#  ${TRAVIS_BUILD_DIR}/install-deps.sh
#  ${TRAVIS_BUILD_DIR}/ci/install-ceph.sh
#  ${TRAVIS_BUILD_DIR}/ci/run.sh
#fi

#./doc/build.sh
#
## start ceph
#if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
#  ci/micro-osd.sh /tmp/osd
#  CEPH_CONF=/tmp/osd/ceph.conf ceph status
#fi
#
#if [ "${RUN_COVERAGE}" == 1 ]; then
#  cmake -DCMAKE_INSTALL_PREFIX=/usr -DCMAKE_BUILD_TYPE=Coverage .
#else
#  mkdir build
#  pushd build
#  if [ "${TRAVIS_OS_NAME}" == "osx" ]; then
#    cmake -DCMAKE_INSTALL_PREFIX=/usr/local -DCMAKE_BUILD_TYPE=Debug ..
#  else
#    cmake -DCMAKE_INSTALL_PREFIX=/usr -DCMAKE_BUILD_TYPE=Debug ..
#  fi
#fi
#
#make -j2
#sudo make install
#
#zlog-test-ram
#zlog-db-test
#
## on linux we assume a ceph instance is running and execute any tests that
## depend on the ceph backend being available.
#if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
#  CEPH_CONF=/tmp/osd/ceph.conf zlog-seqr --streams --port 5678 --daemon
#  CEPH_CONF=/tmp/osd/ceph.conf zlog-test-ceph
#fi
#
#if [ "${RUN_COVERAGE}" == 1 ]; then
#  make zlog-db-test-cov
#  make zlog-test-ram-cov
#  if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
#    CEPH_CONF=/tmp/osd/ceph.conf make zlog-test-ceph-cov
#  fi
#else
#  popd
#fi
