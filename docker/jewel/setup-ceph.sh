#!/bin/bash
set -e
set -x

this_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

PULL_DOCKER=false

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
    -c|--ceph-node)
      if [ -z "$CEPH_NODES" ]; then CEPH_NODES="$2";
      else CEPH_NODES="$CEPH_NODES $2"; fi
      shift
      ;;
    --pool)
      POOL="$2"
      shift
      ;;
    --numpgs)
      NUM_PGS="$2"
      shift
      ;;
    --repl)
      REPL="$2"
      shift
      ;;
    --pull-image)
      PULL_DOCKER=true
      ;;
    *)
      echo "Unknown option $2"
      exit 1
      ;;
  esac
  shift # past argument or value
done 

# create list of ceph nodes without duplicates
CEPH_NODES=$(echo "$MON $OSDS $CEPH_NODES" | xargs -n1 | sort -u | xargs)

echo "######## SETTINGS ########"
echo " MON: $MON"
echo "OSDS: $OSDS"
echo "DDEV: $DDEV"
echo "JDEV: $JDEV"
echo "NOOP: $NOOP_DEVS"
echo "POOL: $POOL"
echo "NPGS: $NUM_PGS"
echo "REPL: $REPL"
echo "CEPH NODES: $CEPH_NODES"
echo "PULL DOCKER: $PULL_DOCKER"
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

if [ -z "$POOL" ]; then
  echo "No pool specified"
  exit 1
fi

if [ -z "$NUM_PGS" ]; then
  echo "Num PGs not specified"
  exit 1
fi

if [ -z "$REPL" ]; then
  echo "Replication factor not specified"
  exit 1
fi

if [ -z "$CEPH_NODES" ]; then
  echo "Looks like nothing to do..."
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
  for host in $CEPH_NODES; do
    echo -n "testing password-less ssh for $host... "
    if ! ssh -oBatchMode=yes -q $host exit; then
      echo "\npassword-less ssh not setup for $host"
      exit 1
    fi
    echo "OK"
  done

  # install ceph
  for host in $CEPH_NODES; do
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
  sudo ${this_dir}/install-docker.sh

  plugin_dir=`mktemp -d`
  trap 'rm -rf "$plugin_dir"' EXIT

  # TODO: this flag should also force refresh the cls plugin below
  if [ "$PULL_DOCKER" = true ]; then
    echo "Pulling fresh docker image"
    sudo docker pull zlog/zlog:jewel
  fi

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
for host in $CEPH_NODES; do
ssh $host <<-'ENDSSH'
  host=`hostname`
  shorthost=`hostname --short`

  sudo stop ceph-all || true
  sudo stop ceph-all || true

  for id in `ps aux | grep '[c]eph-osd' | sed -n 's/.*ceph-osd.* -i \([0-9]\+\).*/\1/p'`; do
    sudo stop ceph-osd id=$id || true
  done

  echo "$host: shutting down services"
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

  echo "$host: unmounting"
  sudo find /var/lib/ceph -mindepth 1 -maxdepth 2 -type d -exec umount {} \; || true

  echo "$host: cleaning up dirs"
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

  # removes the auth lines which we'll put back next
  cp ceph.conf ceph.conf.orig
  #sed -i '/auth_.*_required = cephx/d' ./ceph.conf

  ## add in our stuff
  cat ${this_dir}/jewel.ceph.conf >> ceph.conf

  # setup monitor
  ceph-deploy mon create-initial

  # nuke osd disks
  for host in $OSDS; do
    ceph-deploy disk zap $host:$DDEV
    if [ -n "$JDEV" ]; then
      ceph-deploy disk zap $host:$JDEV
    fi
  done

  # set noop sched
  for host in $OSDS; do
    for dev in $NOOP_DEVS; do
      ssh $host "( echo noop | sudo tee /sys/block/$dev/queue/scheduler )"
    done
  done

  # create osds
  for host in $OSDS; do
    osd_cmd="ceph-deploy osd create $host:$DDEV"
    if [ -n "$JDEV" ]; then
      osd_cmd="$osd_cmd:$JDEV"
    fi
    eval $osd_cmd
  done

  # make life easy
  for host in $CEPH_NODES; do
    ceph-deploy admin $host
    ssh $host sudo chmod a+r /etc/ceph/ceph.client.admin.keyring
  done

  # remove existing pools
  ceph osd pool delete data data --yes-i-really-really-mean-it || true
  ceph osd pool delete metadata metadata --yes-i-really-really-mean-it || true
  ceph osd pool delete rbd rbd --yes-i-really-really-mean-it || true

  # make target pool
  ceph osd pool create $POOL $NUM_PGS $NUM_PGS replicated
  ceph osd pool set $POOL size $REPL
  ceph osd pool set $POOL min_size $REPL

  popd
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
