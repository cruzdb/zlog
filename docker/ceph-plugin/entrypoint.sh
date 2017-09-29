#!/bin/bash

set -e
set -x

if [ ! -d "/src/zlog" ]; then
  git clone --recursive https://github.com/noahdesu/zlog /src/zlog
fi

dir=$(mktemp -d)
pushd $dir
# need the libdir here because otherwise the libraries are put in location based
# on a combination of the distribution and whatever the cmake gnu dirs plugin
# think is best. otherwise, we can't have the hard coded bath below when we copy
# out the plugin to the mounted volume.
cmake -DCMAKE_INSTALL_LIBDIR=/usr/lib /src/zlog
make -j$(nproc) cls_zlog

pushd src/storage/ceph
make install
popd
popd

cp -a /usr/lib/rados-classes/libcls_zlog.so* /ceph_plugin/
