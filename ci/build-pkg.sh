#!/bin/bash
set -e
set -x

if test $(id -u) != 0 ; then
  SUDO=sudo
fi

function rpms() {
  yumdnf="yum"
  if command -v dnf > /dev/null; then
    yumdnf="dnf"
  fi

  # currently assumes fedora
  $SUDO $yumdnf install -y git bzip2 fedpkg
}

source /etc/os-release
case $ID in
  fedora)
    rpms
    ;;

  *)
    echo "$ID not supported. Install dependencies manually."
    exit 1
    ;;
esac

mkdir /tmp/zlog_staging
OUTDIR=/tmp/zlog_staging ./make-dist.sh
cd /tmp/zlog_staging/zlog
fedpkg --release f30 local

# copy into the docker volume
cp -a /tmp/zlog_staging/zlog/x86_64/*.rpm /tmp/zlog_build/
