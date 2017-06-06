#!/bin/bash

set -e
set -x

# install ceph plugin sdk
/install-ceph.sh

# basic dependencies
source /etc/os-release
case $ID in
  debian|ubuntu)
    apt-get install -y git cmake libprotobuf-dev \
        protobuf-compiler libboost-system-dev \
        libboost-program-options-dev liblmdb-dev g++
    ;;

  centos|fedora)
    yum install -y git cmake make gcc-c++ boost-devel \
        protobuf-devel protobuf-compiler lmdb-devel
    ;;

  *)
    echo "unknown os distribution"
    exit 1
    ;;
esac

mkdir -p /src
git clone --recursive https://github.com/noahdesu/zlog.git /src/zlog
pushd /src/zlog
mkdir build
pushd build
cmake ..
make -j$(nproc) cls_zlog
cp -a src/libzlog/backend/libcls_zlog.so* /plugin-output/
popd
popd
