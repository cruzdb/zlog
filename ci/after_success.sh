#!/bin/bash

set -e

if [ "${RUN_COVERAGE}" == 1 ]; then
  pushd build
  coveralls --exclude src/googletest --exclude src/proto \
    --exclude src/kvstore/kvstore.pb.h --exclude src/kvstore/kvstore.pb.cc \
    --gcov-options '\-lp'
  popd
fi
