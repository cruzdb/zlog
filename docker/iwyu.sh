#!/bin/bash
set -e
set -x

# see run-static-analysis.sh

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

BUILD_DIR=$(mktemp -d)
trap "rm -rf ${BUILD_DIR}" EXIT

pushd ${BUILD_DIR}
cmake -DWITH_JNI=ON -DWITH_CEPH=ON ${ZLOG_DIR}
make -j$(nproc)
/usr/src/iwyu/iwyu_tool.py -p .
popd
