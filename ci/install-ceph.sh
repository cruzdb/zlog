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

    ceph_ver=luminous
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

$SUDO cat <<EOF > /etc/yum.repos.d/ceph.conf
[ceph]
name=Ceph packages for $basearch
baseurl=https://download.ceph.com/rpm-luminous/el7/$basearch
enabled=1
priority=2
gpgcheck=1
gpgkey=https://download.ceph.com/keys/release.asc

[ceph-noarch]
name=Ceph noarch packages
baseurl=https://download.ceph.com/rpm-luminous/el7/noarch
enabled=1
priority=2
gpgcheck=1
gpgkey=https://download.ceph.com/keys/release.asc

[ceph-source]
name=Ceph source packages
baseurl=https://download.ceph.com/rpm-luminous/el7/SRPMS
enabled=0
priority=2
gpgcheck=1
gpgkey=https://download.ceph.com/keys/release.asc
EOF

    $SUDO yum install -y librados2-devel
    ;;

  *)
    ;;
esac
