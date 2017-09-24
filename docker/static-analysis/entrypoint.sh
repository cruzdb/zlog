#!/bin/bash
set -e
set -x

./install-deps.sh
ci/install-ceph.sh
apt-get install -y rados-objclass-dev

function run_scan_build() {
  local bdir=$(mktemp -d)
  trap "rm -rf ${bdir}" EXIT

  # clang check
  pushd ${bdir}
  scan-build-4.0 \
    cmake \
    -DWITH_JNI=ON \
    -DWITH_CEPH=ON \
    /src/zlog

  scan-build-4.0 \
    -o /results/scanbuild \
    make -j$(nproc)
  popd

  ls -l /results
  rm -rf ${bdir}
}

function run_iwyu() {
  local bdir=$1
  /usr/src/iwyu/iwyu_tool.py -p ${bdir} | tee /results/iwyu.txt
}

function run_cppcheck() {
  local bdir=$1
  cppcheck \
    --force \
    --inconclusive \
    --enable=all \
    --std=c++11 \
    --quiet \
    -I${bdir}/src \
    -I${bdir}/src/storage/ceph \
    -I${bdir}/src/java/native \
    -I/src/zlog/src \
    -I/src/zlog/src/include \
    -I/src/zlog/src/spdlog/include \
    -I/src/zlog/src/rapidjson/include \
    -I/src/zlog/src/googletest/googletest/include \
    -i${bdir} \
    -i/src/zlog/src/spdlog \
    -i/src/zlog/src/rapidjson \
    -i/src/zlog/src/googletest \
    -i/src/zlog/src/kvstore/persistent-rbtree.cc \
    /src/zlog 2>&1 | tee /results/cppcheck.txt
}

run_scan_build

bdir=$(mktemp -d)
trap "rm -rf ${bdir}" EXIT

pushd ${bdir}
cmake -DWITH_JNI=ON -DWITH_CEPH=ON /src/zlog
make -j$(nproc)
popd

run_iwyu $bdir
run_cppcheck $bdir

rm -rf ${bdir}
