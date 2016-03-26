#!/bin/bash

set -x
set -e

HOST=$1
CDIR=$2
DDEV=$3
JDEV=$4
POOL=$5
PGNUM=$6

# stop ceph and clean-up everything
sudo stop ceph-all || true
ceph-deploy purge $HOST
ceph-deploy purgedata $HOST

# setup cluster control dir
rm -rf $CDIR
mkdir $CDIR
pushd $CDIR

ceph-deploy new $HOST

# removes the auth lines which we'll put back next
sed -i '/auth_.*_required = cephx/d' ./ceph.conf

# add in our ceph configuration bits
cat <<EOF >> ceph.conf
# AUTH
auth service required = none
auth cluster required = none
auth client required = none
auth supported = none
ms crc data = false
ms crc header = false
throttler perf count = false
objecter_inflight_ops = 24000
objecter_inflight_op_bytes = 1048576000
ms_dispatch_throttle_bytes = 0

# OSD STUFF
max open files = 131072
osd pool default pg num = 128
osd pool default pgp num = 128
osd pool default size = 1
osd pool default min size = 1
osd crush chooseleaf type = 0

# SCRUB STUFF
osd max scrubs = 0
osd_scrub_min_interval = 604800
osd deep scrub interval = 604800
mon scrub interval = 604800

# DEBUG
debug_lockdep = 0/0
debug_context = 0/0
debug_crush = 0/0
debug_buffer = 0/0
debug_timer = 0/0
debug_filer = 0/0
debug_objecter = 0/0
debug_rados = 0/0
debug_rbd = 0/0
debug_journaler = 0/0
debug_objectcatcher = 0/0
debug_client = 0/0
debug_osd = 0/0
debug_optracker = 0/0
debug_objclass = 0/0
debug_filestore = 0/0
debug_journal = 0/0
debug_ms = 0/0
debug_monc = 0/0
debug_tp = 0/0
debug_auth = 0/0
debug_finisher = 0/0
debug_heartbeatmap = 0/0
debug_perfcounter = 0/0
debug_asok = 0/0
debug_throttle = 0/0
debug_mon = 0/0
debug_paxos = 0/0
debug_rgw = 0/0

[osd]
osd mkfs type = xfs
osd mkfs options xfs = -f -i size=2048
osd mount options xfs = noatime,largeio,inode64,swalloc
osd mon heartbeat interval = 30
filestore merge threshold = 40
filestore split multiple = 8
osd op threads = 8
filestore op threads = 8
filestore max sync interval = 5
osd max scrubs = 0
osd objectstore = filestore
osd crush update on start = true

osd enable op tracker = false
filestore wbthrottle enable = false
filestore_queue_max_bytes = 1048576000
filestore_queue_max_ops = 500
journal_queue_max_bytes = 1048576000
journal_queue_max_ops = 3000
osd_op_num_shards = 10
EOF

# install ceph
retries=0
until [ $retries -ge 9 ]; do
  ceph-deploy install --release hammer $HOST && break
  retries=$[$retries+1]
  sleep 600
done

retries=0
until [ $retries -ge 9 ]; do
  ceph-deploy pkg --install librados-dev $HOST && break
  retries=$[$retries+1]
  sleep 600
done

if [ ! -e /usr/bin/ceph ]; then
  echo "ceph not installed"
  exit 1
fi

if [ ! -e /usr/include/rados/librados.hpp ]; then
  echo "rados-dev not installed"
  exit 1
fi

# setup and start
ceph-deploy mon create-initial
ceph-deploy disk zap $HOST:$DDEV
ceph-deploy disk zap $HOST:$JDEV
ceph-deploy osd create $HOST:$DDEV:$JDEV

# wait for ceph health ok
while true; do
  if ceph status | tee /dev/tty | grep -q HEALTH_OK; then
    break
  fi
  sleep 1
done

ceph osd pool create $POOL $PGNUM $PGNUM replicated

# wait for ceph health ok
while true; do
  if ceph status | tee /dev/tty | grep -q HEALTH_OK; then
    break
  fi
  sleep 1
done

ceph osd pool set $POOL size 1

# wait for ceph health ok
while true; do
  if ceph status | tee /dev/tty | grep -q HEALTH_OK; then
    break
  fi
  sleep 1
done
