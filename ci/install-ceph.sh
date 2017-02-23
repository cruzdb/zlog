#!/bin/bash

set -e
set -x

if [[ "$OSTYPE" == "darwin"* ]]; then
  exit 0
fi

if test $(id -u) != 0 ; then
  SUDO=sudo
fi

source /etc/os-release
case $ID in
  debian|ubuntu)
    $SUDO apt-get update

    $SUDO env DEBIAN_FRONTEND=noninteractive \
      apt-get install -y wget curl lsb-release \
      software-properties-common apt-transport-https

    ceph_ver=kraken
    ceph_deb_release=$(lsb_release -sc)
    ceph_http_code=$(curl -o /dev/null --silent --head --write-out '%{http_code}' \
      http://download.ceph.com/debian-${ceph_ver}/dists/${ceph_deb_release}/)
    if [ $ceph_http_code == "404" ]; then
      ceph_deb_release=xenial
    fi

    wget -q -O- 'https://download.ceph.com/keys/release.asc' | $SUDO apt-key add -
    $SUDO apt-add-repository "deb https://download.ceph.com/debian-${ceph_ver}/ ${ceph_deb_release} main"

    $SUDO apt-get update
    $SUDO apt-get install -y librados-dev
    ;;

  centos|fedora)
    $SUDO rpm --import 'https://download.ceph.com/keys/release.asc'
    $SUDO rpm -Uvh --replacepkgs --force \
      https://download.ceph.com/rpm-kraken/el7/noarch/ceph-release-1-0.el7.noarch.rpm

    $SUDO yum install -y librados2-devel
    ;;

  *)
    ;;
esac
