#!/bin/bash

set -e

# start ceph
if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
  ci/micro-osd.sh /tmp/osd
  CEPH_CONF=/tmp/osd/ceph.conf ceph status
fi

if [ "${RUN_COVERAGE}" == 1 ]; then
  cmake -DCMAKE_BUILD_TYPE=Coverage .
else
  mkdir build
  pushd build
  cmake -DCMAKE_BUILD_TYPE=Debug ..
fi

make -j2

./src/test/zlog-test-ram
./src/test/db-test

# on linux we assume a ceph instance is running and execute any tests that
# depend on the ceph backend being available.
if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
  CEPH_CONF=/tmp/osd/ceph.conf ./src/zlog-seqr --streams --port 5678 --daemon
  CEPH_CONF=/tmp/osd/ceph.conf ./src/test/zlog-test-ceph
fi

if [ "${RUN_COVERAGE}" == 1 ]; then
  make db-test-cov
  make zlog-test-ram-cov
  if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
    CEPH_CONF=/tmp/osd/ceph.conf make zlog-test-ceph-cov
  fi
else
  popd
fi
