#!/bin/bash

set -e
set -x

if [ ! -d "/src/zlog" ]; then
  git clone --recursive https://github.com/noahdesu/zlog /src/zlog
fi

dir=$(mktemp -d)
pushd $dir
cmake /src/zlog
make -j$(nproc) cls_zlog

pushd src/storage/ceph
make install
popd
popd

cp -a /usr/lib/rados-classes/libcls_zlog.so* /ceph_plugin/
