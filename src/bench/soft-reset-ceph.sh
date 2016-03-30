#!/bin/bash
set -x
set -e

cdir=$1
pool=$2
pgnum=$3
ddev=$4
version=$5
host=`hostname`
shorthost=`hostname --short`

THIS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

sudo stop ceph-all || true
sudo stop ceph-all || true
sudo stop ceph-osd id=0 || true
sudo stop ceph-mon id=$host || true
sudo stop ceph-mon id=$shorthost || true
sudo skill -9 ceph-osd || true
sudo skill -9 ceph-mon || true
sleep 10

sudo find /var/lib/ceph -mindepth 1 -maxdepth 2 -type d -exec umount {} \; || true

sudo rm -rf /etc/ceph
sudo rm -rf /var/log/ceph
sudo rm -rf /var/lib/ceph/mon
sudo rm -rf /var/lib/ceph/tmp
sudo rm -rf /var/lib/ceph/osd
sudo rm -rf /var/lib/ceph/bootstrap-osd
sudo rm -rf /var/lib/ceph/radosgw
sudo rm -rf /var/lib/ceph/mds
sudo rm -rf /var/lib/ceph/bootstrap-mds
sudo rm -rf /var/lib/ceph/bootstrap-rgw

sudo mkdir /etc/ceph/
sudo mkdir /var/log/ceph/
sudo mkdir /var/lib/ceph/mon/
sudo mkdir /var/lib/ceph/tmp/
sudo mkdir /var/lib/ceph/osd/
sudo mkdir /var/lib/ceph/bootstrap-osd/
sudo mkdir /var/lib/ceph/radosgw/
sudo mkdir /var/lib/ceph/mds/
sudo mkdir /var/lib/ceph/bootstrap-mds/
sudo mkdir /var/lib/ceph/bootstrap-rgw

# setup cluster control dir
rm -rf $cdir
mkdir $cdir
pushd $cdir

ceph-deploy new $host

# removes the auth lines which we'll put back next
sed -i '/auth_.*_required = cephx/d' ./ceph.conf

# add in our ceph configuration bits
if [ "$version" == "hammer" ]; then
  cat ${THIS_DIR}/hammer.conf >> ceph.conf
elif [ "$version" == "jewel" ]; then
  cat ${THIS_DIR}/jewel.conf >> ceph.conf
else
  echo "invalid version $version"
  exit 1
fi

ceph-deploy mon create-initial
ceph-deploy disk zap $host:$ddev
ceph-deploy osd create $host:$ddev

# wait for ceph health ok
while true; do
  if ceph status | tee /dev/tty | grep -q HEALTH_OK; then
    break
  fi
  sleep 1
done

ceph osd pool create $pool $pgnum $pgnum replicated

# wait for ceph health ok
while true; do
  if ceph status | tee /dev/tty | grep -q HEALTH_OK; then
    break
  fi
  sleep 1
done

ceph osd pool set $pool size 1

# wait for ceph health ok
while true; do
  if ceph status | tee /dev/tty | grep -q HEALTH_OK; then
    break
  fi
  sleep 1
done
