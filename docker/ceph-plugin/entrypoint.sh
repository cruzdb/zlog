#!/bin/bash

set -e
set -x

tar xzf ceph.tar.gz

pushd /ceph
git fetch origin
git checkout -b build origin/zlog/master-pb

apt-get update
./install-deps.sh
./do_cmake.sh

pushd build
make -j$(nproc) cls_zlog

rm -rf /ceph_zlog_plugin/*
cp -a lib/libcls_zlog.so* /ceph_zlog_plugin/
