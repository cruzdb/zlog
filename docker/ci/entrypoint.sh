#!/bin/bash
set -e
set -x

# checkout zlog ceph repo
pushd /src/ceph
git remote add nd https://github.com/noahdesu/ceph.git
git fetch nd
git checkout -b zlog/jewel nd/zlog/jewel
git submodule update --force --init --recursive
bash ./install-deps.sh

# build and install zlog object class and client
./autogen.sh
./configure
cd src
make libcls_zlog.la
make libcls_zlog_client.la
cp -a .libs/libcls_zlog.so* /usr/lib/rados-classes/
cp -a .libs/libcls_zlog_client.so* /usr/lib/
cp cls/zlog/cls_zlog_client.h /usr/include/rados/
popd

# startup a ceph cluster
mkdir /tmp/ceph
bash /src/micro-osd.sh /tmp/ceph

BRANCH=${branch:-master}

# build zlog
cd /src

if [ ! -d /src/zlog ]; then
  git clone --branch=$BRANCH https://github.com/noahdesu/zlog.git
fi

cd zlog
git status

autoreconf -ivf
./configure
make

# run seqr and tests
cd /src/zlog/src
export CEPH_CONF=/tmp/ceph/ceph.conf
./zlog-seqr --port 5678 --daemon
./test
