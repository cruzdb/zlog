#!/bin/bash
set -e

# startup a ceph cluster
mkdir /tmp/ceph
bash /src/micro-osd.sh /tmp/ceph

cd /src/zlog/src
export CEPH_CONF=/tmp/ceph/ceph.conf
./zlog-seqr --port 5678 --daemon
./test
