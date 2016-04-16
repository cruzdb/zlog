#!/bin/bash

set -e

# settings
ceph_version=jewel

# context
host=`hostname`
shorthost=`hostname --short`
this_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# defaults
journal_dev=none
noop_devs=""

while [[ $# > 1 ]]; do
  key="$1"
  case $key in
    -d|--data-dev)
      data_dev="$2"
      shift # past argument
      ;;
    -j|--journal-dev)
      journal_dev="$2"
      shift # past argument
      ;;
    -n|--noop)
      noop_devs="$noop_devs $2"
      shift # past argument
      ;;
    *)
      # unknown option
      ;;
  esac
  shift # past argument or value
done 

if [ -z $data_dev ]; then
  echo "must supply a data device (--data-dev)"
  exit 1
fi

function prepare() {
  # install ceph-deploy
  if ! which ceph-deploy &> /dev/null; then
    sudo apt-get -y update
    sudo apt-get -y install \
      git python-virtualenv
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
    echo "Host *\n  StrictHostKeyChecking no" >> ~/.ssh/config
  fi
  
  # check if password-less ssh works
  if ! ssh -oBatchMode=yes -q localhost exit; then
    ssh-keygen -f $HOME/.ssh/id_rsa -t rsa -N ''
    cat ~/.ssh/id_rsa.pub >> ~/.ssh/authorized_keys
    chmod 600 ~/.ssh/authorized_keys
  fi
  
  if ! which ceph &> /dev/null; then
    ceph-deploy install --release ${ceph_version} `hostname`
  fi
  
  if [ ! -e "/usr/include/rados/librados.hpp" ]; then
    ceph-deploy pkg --install librados-dev `hostname`
  fi
}

function reset_ceph_soft() {
  sudo stop ceph-all || true
  sudo stop ceph-all || true
  sudo stop ceph-osd id=0 || true
  sudo stop ceph-mon id=$host || true
  sudo stop ceph-mon id=$shorthost || true
  sudo skill -9 ceph-osd || true
  sudo skill -9 ceph-mon || true

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
}

function create_ceph_and_start() {
  cdir=`mktemp -d`
  pushd $cdir

  # start new ceph cluster
  ceph-deploy new $host
  
  # removes the auth lines which we'll put back next
  sed -i '/auth_.*_required = cephx/d' ./ceph.conf
  
  # add in our ceph configuration bits
  if [ "$ceph_version" == "jewel" ]; then
    cat ${this_dir}/jewel.conf >> ceph.conf
  else
    echo "invalid version $ceph_version"
    exit 1
  fi
  
  # setup monitor
  ceph-deploy mon create-initial
  
  # clean up storage devices
  ceph-deploy disk zap $host:$data_dev
  if [ "$journal_dev" != "none" ]; then
    ceph-deploy disk zap $host:$journal_dev
  fi
  
  # set scheduler for devices
  for dev in $noop_devs; do
    echo "Setting noop scheduler for: $dev"
    echo noop | sudo tee /sys/block/$dev/queue/scheduler
    echo "Scheduler ($dev): $(cat /sys/block/$dev/queue/scheduler)"
  done
  
  # create osd
  if [ "$journal_dev" != "none" ]; then
    ceph-deploy osd create $host:$data_dev:$journal_dev
  else
    ceph-deploy osd create $host:$data_dev
  fi

  popd
}

function wait_health_ok() {
  while true; do
    if ceph status | tee /dev/tty | grep -q HEALTH_OK; then
      if ! ceph status | grep -q creating &> /dev/null; then
        break
      fi
    fi
    sleep 1
  done
}

prepare
reset_ceph_soft
create_ceph_and_start
wait_health_ok
