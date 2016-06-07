#!/bin/bash
set -e

while [[ $# > 1 ]]; do
  key="$1"
  case $key in
    -m|--mon)
      MON="$2"
      shift # past argument
      ;;
    -o|--osd)
      if [ -z "$OSDS" ]; then OSDS="$2";
      else OSDS="$OSDS $2"; fi
      shift
      ;;
    -d|--data-dev)
      DDEV="$2"
      shift
      ;;
    -j|--journal-dev)
      JDEV="$2"
      shift
      ;;
    -n|--noop-dev)
      if [ -z "$NOOP_DEVS" ]; then NOOP_DEVS="$2";
      else NOOP_DEVS="$NOOP_DEVS $2"; fi
      shift
      ;;
    *)
      echo "Unknown option $2"
      exit 1
      ;;
  esac
  shift # past argument or value
done 

echo "######## SETTINGS ########"
echo " MON: $MON"
echo "OSDS: $OSDS"
echo "DDEV: $DDEV"
echo "JDEV: $JDEV"
echo "NOOP: $NOOP_DEVS"
echo "##########################"

if [ -z "$MON" ]; then
  echo "No monitor specified"
  exit 1
fi

if [ -z "$OSDS" ]; then
  echo "No OSDs specified"
  exit 1
fi

if [ -z "$DDEV" ]; then
  echo "No data device specified"
  exit 1
fi

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

  # extract and install Ceph plugin bits
  sudo ./install-docker.sh

  plugin_dir=`mktemp -d`
  trap 'rm -rf "$plugin_dir"' EXIT

  sudo docker pull zlog/zlog:jewel
  sudo docker run --rm -it -v $plugin_dir:/tmp/foo zlog/zlog:jewel \
    cp /usr/lib/rados-classes/libcls_zlog.so /tmp/foo

  for host in $OSDS; do
    echo -n "checking for zlog plugin on $host... "
    if ! ssh $host stat /usr/lib/rados-classes/libcls_zlog.so &> /dev/null; then
      echo "installing libcls_zlog.so plugin"
      rsync -av -e ssh --rsync-path="sudo rsync" $plugin_dir/libcls_zlog.so \
        ${host}:/usr/lib/rados-classes/libcls_zlog.so
    else
      echo "OK"
    fi
  done
}

function reset_ceph() {
for host in $MON $OSDS; do
ssh $host <<-'ENDSSH' &> /dev/null
  host=`hostname`
  shorthost=`hostname --short`

  sudo stop ceph-all || true
  sudo stop ceph-all || true

  for id in `ps aux | grep '[c]eph-osd' | sed -n 's/.*ceph-osd.* -i \([0-9]\+\).*/\1/p'`; do
    sudo stop ceph-osd id=$id || true
  done

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

  # nuke osd disks
  zap_cmd="ceph-deploy disk zap {$(echo $OSDS | sed "s/ /,/g")}"
  eval "$zap_cmd:$DDEV"
  if [ -n "$JDEV" ]; then
    eval "$zap_cmd:$JDEV"
  fi

  # set noop sched
  for host in $OSDS; do
    for dev in $NOOP_DEVS; do
      ssh $host "( echo noop | sudo tee /sys/block/$dev/queue/scheduler )"
    done
  done

  # create osds
  osd_cmd="ceph-deploy osd create {$(echo $OSDS | sed "s/ /,/g")}:$DDEV"
  if [ -n "$JDEV" ]; then
    osd_cmd="$osd_cmd:$JDEV"
  fi
  eval $osd_cmd

  # make life easy
  eval "ceph-deploy admin {$(echo "$MON $OSDS" | sed "s/ /,/g")}"
  for host in $MON $OSDS; do
    ssh $host sudo chmod a+r /etc/ceph/ceph.client.admin.keyring
  done
}

function wait_healthy() {
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
reset_ceph
setup_ceph
wait_healthy
