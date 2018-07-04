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

    ceph_ver=mimic
    ceph_deb_release=$(lsb_release -sc)
    ceph_http_code=$(curl -o /dev/null --silent --head --write-out '%{http_code}' \
      http://download.ceph.com/debian-${ceph_ver}/dists/${ceph_deb_release}/)
    if [ $ceph_http_code == "404" ]; then
      ceph_deb_release=xenial
    fi

    wget -q -O- 'https://download.ceph.com/keys/release.asc' | $SUDO apt-key add -
    $SUDO apt-add-repository "deb https://download.ceph.com/debian-${ceph_ver}/ ${ceph_deb_release} main"

    
    $SUDO apt-get update
    $SUDO env DEBIAN_FRONTEND=noninteractive \
      apt-get install -y -- librados-dev ceph
    ;;

  centos|fedora)
    yumdnf="yum"
    if command -v dnf > /dev/null; then
      yumdnf="dnf"
    fi

    $SUDO $yumdnf install -y redhat-lsb-core
    case $(lsb_release -si) in
      Fedora)
        ;;

      CentOS)
        $SUDO rpm --import 'https://download.ceph.com/keys/release.asc'

        # NOTE: I had been naming this file ceph.conf rather than ceph.repo, and
        # didn't notice that yum/dnf wasn't picking up the repo information. This
        # manifest as protocol incompatabilities with older versions of ceph found
        # in the default fedora/centos repositories. The second gotcha was disabling
        # variable substitution in the heredoc. The result was that the URLs didn't
        # have the appened `$basearch` variable in the ceph.repo file and all the
        # yum/dnf repo cache synchronization steps were failing.
cat <<'EOF' | $SUDO tee /etc/yum.repos.d/ceph.repo
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
        ;;
      *)
        echo "unknown release"
        exit 1
        ;;
    esac

    $SUDO yum repolist
    # make sure to name this librados-devel, rather than what had been here
    # which is librados2-devel. The later was valid in the default repos of
    # older distributions. The effect was that even after we were successfully
    # getting the ceph repo to be picked up by yum/dnf, this naming was still
    # wrong and an old version of ceph was being installed!
    $SUDO yum install -y librados-devel ceph
    ;;

  *)
    echo "$ID not supported. Install dependencies manually."
    exit 1
    ;;
esac
