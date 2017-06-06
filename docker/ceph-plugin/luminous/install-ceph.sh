#!/bin/bash

set -e
set -x

source /etc/os-release
case $ID in
  debian|ubuntu)
    export DEBIAN_FRONTEND=noninteractive
    apt-get update
    apt-get install -y wget lsb-release \
      software-properties-common apt-transport-https

    codename=$(lsb_release -sc)
    wget -q -O- 'https://download.ceph.com/keys/release.asc' | apt-key add -
    apt-add-repository "deb https://download.ceph.com/debian-luminous/ ${codename} main"
    apt-get update
    apt-get install -y rados-objclass-dev
    ;;

  centos)
    yum install -y https://dl.fedoraproject.org/pub/epel/epel-release-latest-7.noarch.rpm

    cat <<'EOF' > /etc/yum.repos.d/ceph.repo
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

    yum install -y rados-objclass-devel
    ;;

  fedora)

    cat <<'EOF' > /etc/yum.repos.d/ceph.repo
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

    dnf install -y rados-objclass-devel
    ;;

  *)
    echo "unknown os distribution"
    exit 1
    ;;
esac

exit 0
