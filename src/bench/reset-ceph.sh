#!/bin/bash

set -x
set -e

HOST=$1
CDIR=$2
DDEV=$3
JDEV=$4
POOL=$5
PGNUM=$6
VERSION=$7

THIS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# stop ceph and clean-up everything
sudo stop ceph-all || true
sudo stop ceph-all || true
sudo stop ceph-osd id=0 || true
sudo stop ceph-mon id=$HOST || true
sudo skill -9 ceph-osd || true
sudo skill -9 ceph-mon || true
sleep 10

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
if [ "$VERSION" == "hammer" ]; then
  cat ${THIS_DIR}/hammer.conf >> ceph.conf
elif [ "$VERSION" == "jewel" ]; then
  cat ${THIS_DIR}/jewel.conf >> ceph.conf
else
  echo "invalid version $VERSION"
  exit 1
fi

# install ceph
retries=0
until [ $retries -ge 9 ]; do
  ceph-deploy install --release $VERSION $HOST && break
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
