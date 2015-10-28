#!/bin/bash
set -e

# startup a ceph cluster
mkdir /tmp/ceph
bash /src/micro-osd.sh /tmp/ceph

# install zlog. this is done in the entry point so it will
# pull the latest zlog source each time the container is run
cd /src
apt-get install -y libprotobuf-dev protobuf-compiler
git clone https://github.com/noahdesu/zlog.git
cd zlog
autoreconf -ivf
./configure
make

cd /src/zlog/src
export CEPH_CONF=/tmp/ceph/ceph.conf
./zlog-seqr --port 5678 --daemon
./test
