#!/bin/bash

set -e
set -x

pushd /ceph
git fetch origin
git checkout origin/zlog/master-pb

./do_cmake.sh

pushd build
make -j$(nproc) cls_zlog

rm -rf /ceph_zlog_plugin/*
cp -a lib/libcls_zlog.so* /ceph_zlog_plugin/
