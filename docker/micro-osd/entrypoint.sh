#!/bin/bash

set -e
set -x

dir=$(mktemp -d)
pushd $dir
cmake /src/zlog
make -j$(nproc) cls_zlog

pushd src/libzlog/backend
make install
popd
popd

/micro-osd.sh /micro-osd
