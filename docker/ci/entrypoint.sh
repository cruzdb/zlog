#!/bin/bash
set -e
set -x

# startup a ceph cluster
mkdir /tmp/ceph
bash /src/micro-osd.sh /tmp/ceph

BRANCH=${branch:-master}

apt-get install -y libprotobuf-dev protobuf-compiler

# install zlog. this is done in the entry point so it will
# pull the latest zlog source each time the container is run
cd /src

ls -l

if [ ! -d /src/zlog ]; then
  git clone --branch=$BRANCH https://github.com/noahdesu/zlog.git
fi

cd zlog
git status

autoreconf -ivf
./configure
make

cd /src/zlog/src
export CEPH_CONF=/tmp/ceph/ceph.conf
./zlog-seqr --port 5678 --daemon
./test
