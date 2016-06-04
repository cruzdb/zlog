#!/bin/bash
set -e

MON="c220g2-011327.wisc.cloudlab.us"
OSDS="c220g2-011331.wisc.cloudlab.us c220g2-011330.wisc.cloudlab.us"
DDEV=sdb
JDEV=sdc
NOOP_DEVS="sdc"

function prepare() {
  # install ceph-deploy
  if ! which ceph-deploy &> /dev/null; then
    sudo apt-get -y update
    sudo apt-get -y install git python-virtualenv
    if [ ! -d ceph-deploy ]; then
      git clone https://github.com/ceph/ceph-deploy
    fi
    pushd ceph-deploy
    ./bootstrap
    sudo ln -sf $PWD/ceph-deploy /usr/bin/ceph-deploy
    popd
  fi

  # don't worry about ssh keys
  if ! grep "StrictHostKeyChecking" ~/.ssh/config &> /dev/null; then
    printf "Host *\n  StrictHostKeyChecking no" >> ~/.ssh/config
  fi

  # make sure hosts support password-less ssh
  for host in $MON $OSDS; do
    echo -n "testing password-less ssh for $host... "
    if ! ssh -oBatchMode=yes -q $host exit; then
      echo "\npassword-less ssh not setup for $host"
      exit 1
    fi
    echo "OK"
  done

  # install ceph
  for host in $MON $OSDS; do
    echo -n "checking ceph installation on $host... "
    if ! ssh $host which ceph &> /dev/null; then
      echo "installing ceph"
      ceph-deploy install --release jewel $host
    else
      echo "OK"
    fi
    echo -n "checking rados-dev installation on $host... "
    if ! ssh $host stat /usr/include/rados/librados.hpp &> /dev/null; then
      echo "installing rados-dev"
      ceph-deploy pkg --install librados-dev $host
    else
      echo "OK"
    fi
  done
}

# TODO: figure out the id=0 etc...
function reset_ceph() {
for host in $MON $OSDS; do
ssh $host <<-'ENDSSH' &> /dev/null
  host=`hostname`
  shorthost=`hostname --short`
  sudo stop ceph-all || true
  sudo stop ceph-all || true
  sudo stop ceph-osd id=0 || true
  sudo stop ceph-mon id=$host || true
  sudo stop ceph-mon id=$shorthost || true
  sudo service ceph-osd-all stop || true
  sudo service ceph-osd-all stop || true
  sudo service ceph-mon-all stop || true
  sudo service ceph-mon-all stop || true
  sudo skill -9 ceph-osd || true
  sudo skill -9 ceph-mon || true
  sudo /etc/init.d/ceph stop || true
  sleep 5

  sudo find /var/lib/ceph -mindepth 1 -maxdepth 2 -type d -exec umount {} \; || true

  sudo find /etc/ceph/ -mindepth 1 -exec rm -rf {} \; || true
  sudo find /var/log/ceph/ -mindepth 1 -exec rm -rf {} \; || true
  sudo find /var/lib/ceph/mon/ -mindepth 1 -exec rm -rf {} \; || true
  sudo find /var/lib/ceph/tmp/ -mindepth 1 -exec rm -rf {} \; || true
  sudo find /var/lib/ceph/osd/ -mindepth 1 -exec rm -rf {} \; || true
  sudo find /var/lib/ceph/bootstrap-osd/ -mindepth 1 -exec rm -rf {} \; || true
  sudo find /var/lib/ceph/radosgw/ -mindepth 1 -exec rm -rf {} \; || true
  sudo find /var/lib/ceph/mds/ -mindepth 1 -exec rm -rf {} \; || true
  sudo find /var/lib/ceph/bootstrap-mds/ -mindepth 1 -exec rm -rf {} \; || true
  sudo find /var/lib/ceph/bootstrap-rgw/ -mindepth 1 -exec rm -rf {} \; || true
ENDSSH
done
}

function setup_ceph() {
  cdir=`mktemp -d`
  pushd $cdir
  
  # start new ceph cluster
  ceph-deploy new $MON

  # setup monitor
  ceph-deploy mon create-initial

  cd_osd_list="{$(echo $OSDS | sed "s/ /,/g")}"

  # nuke osd disks
  ceph-deploy disk zap $cd_osd_list:$DDEV
  if [ -n "$JDEV" ]; then
    ceph-deploy disk zap $cd_osd_list:$JDEV
  fi

  # set noop sched
  for host in $OSDS; do
    for dev in $NOOP_DEVS; do
      ssh $host "( echo noop | sudo tee /sys/block/$dev/queue/scheduler )"
    done
  done

  cd_osd_devs="$DDEV"
  if [ -n "$JDEV" ]; then
    cd_osd_devs="$cd_osd_devs:$JDEV"
  fi

  ceph-deploy osd create $cd_osd_list:$cd_osd_devs
}

function wait_healthy() {
ssh $MON <<-'ENDSSH'
  while true; do
    if ceph status | tee /dev/tty | grep -q HEALTH_OK; then
      if ! ceph status | grep -q creating &> /dev/null; then
        break
      fi
    fi
    sleep 1
  done
ENDSSH
}

prepare
reset_ceph
setup_ceph
wait_healthy
