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
    -v|--version)
      ceph_version="$2"
      shift
      ;;
    -b|--bluestore)
      bluestore=yes
      shift
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

echo "====================================="
echo "              CONFIG"
echo "====================================="
echo " DATA-DEV: $data_dev"
echo " JRNL-DEV: $journal_dev"
echo " NOOP-DEV: $noop_devs"
echo "  VERSION: $ceph_version"
echo "BLUESTORE: $bluestore"
echo "====================================="

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
    printf "Host *\n  StrictHostKeyChecking no" >> ~/.ssh/config
  fi
  
  # check if password-less ssh works
  if ! ssh -oBatchMode=yes -q localhost exit; then
    ssh-keygen -f $HOME/.ssh/id_rsa -t rsa -N ''
    cat ~/.ssh/id_rsa.pub >> ~/.ssh/authorized_keys
    chmod 600 ~/.ssh/authorized_keys
  fi
  
  if ! which ceph &> /dev/null; then
    if [ "${ceph_version}" == "master" ]; then
      ceph-deploy install --dev ${ceph_version} `hostname`
    else
      ceph-deploy install --release ${ceph_version} `hostname`
    fi
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
}

function create_ceph_and_start() {
  # base ceph conf
  conf_extra="__dne__"
  if [ "$ceph_version" == "jewel" ]; then
    conf_extra=${this_dir}/jewel
  elif [ "$ceph_version" == "master" ]; then
    conf_extra=${this_dir}/jewel
  elif [ "$ceph_version" == "firefly" ]; then
    conf_extra=${this_dir}/firefly
  else
    echo "invalid version $ceph_version"
    exit 1
  fi
  if [ "x$bluestore" == "xyes" ]; then
    conf_extra=${conf_extra}-bluestore
    osd_create_opts="--bluestore"
  fi
  conf_extra=${conf_extra}.conf

  cdir=`mktemp -d`
  pushd $cdir

  # start new ceph cluster
  ceph-deploy new $host
  
  # removes the auth lines which we'll put back next
  sed -i '/auth_.*_required = cephx/d' ./ceph.conf
  
  # add in our stuff
  cat $conf_extra >> ceph.conf
  
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
    ceph-deploy osd create $osd_create_opts $host:$data_dev:$journal_dev
  else
    ceph-deploy osd create $osd_create_opts $host:$data_dev
  fi

  sudo stop ceph-osd id=0 || true
  sudo stop ceph-osd id=0 || true
  sudo chown ceph:ceph /var/log/ceph/ceph-osd.0.log || true
  sudo start ceph-osd id=0 || true

  # created in firefly
  ceph osd pool delete data data --yes-i-really-really-mean-it || true
  ceph osd pool delete metadata metadata --yes-i-really-really-mean-it || true

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
