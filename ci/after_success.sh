#!/bin/bash

set -e

if [ "${RUN_COVERAGE}" == 1 ]; then
  coveralls --exclude src/googletest --exclude src/proto \
    --exclude src/kvstore/kvstore.pb.h --exclude src/kvstore/kvstore.pb.cc \
    --gcov-options '\-lp'
fi
