#!/bin/bash

set -e

# we don't run any tests for a coverity build
if [ "${COVERITY_SCAN_BRANCH}" == 1 ]; then
  exit 0
fi

if [ "${COVERAGE}" == 1 ]; then
  cmake -DCMAKE_BUILD_TYPE=Coverage .
  make
  make db-test-cov
  make zlog-test-ram-cov
  coveralls --exclude src/googletest --exclude src/proto \
    --exclude src/kvstore/kvstore.pb.h --exclude src/kvstore/kvstore.pb.cc \
    --gcov-options '\-lp'
else
  docker run -v $TRAVIS_BUILD_DIR:/src/zlog zlog/ci
fi
