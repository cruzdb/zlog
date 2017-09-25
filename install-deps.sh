#!/bin/bash

# adapted from https://github.com/ceph/ceph/blob/master/install-deps.sh

set -e

if [[ "$OSTYPE" == "darwin"* ]]; then
  brew install boost protobuf cmake lmdb || true
  exit 0
fi

ZLOG_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if test $(id -u) != 0 ; then
  SUDO=sudo
fi

source /etc/os-release
case $ID in
  debian|ubuntu)
    $SUDO apt-get update

    $SUDO env DEBIAN_FRONTEND=noninteractive \
      apt-get install -y devscripts equivs

    # run mk-build-deps in tmp dir to avoid creation of artifact files that
    # cause errors for read-only docker mounts
    tmp=$(mktemp -d)
    pushd $tmp
    $SUDO env DEBIAN_FRONTEND=noninteractive \
      mk-build-deps --install --remove \
      --tool="apt-get -y --no-install-recommends" \
      ${ZLOG_DIR}/debian/control || exit 1
    popd
    rm -rf $tmp

    $SUDO env DEBIAN_FRONTEND=noninteractive \
      apt-get -y remove zlog-build-deps

    # for doc/build.sh
    $SUDO env DEBIAN_FRONTEND=noninteractive \
      apt-get install -y python-virtualenv
    ;;

  centos|fedora)
    BUILD_DIR=$(mktemp -d)
    trap "rm -fr $BUILD_DIR" EXIT

    yumdnf="yum"
    builddepcmd="yum-builddep -y"
    if command -v dnf > /dev/null; then
      yumdnf="dnf"
      $SUDO dnf install -y 'dnf-command(builddep)'
      builddepcmd="dnf -y builddep --allowerasing"
    fi

    $SUDO $yumdnf install -y redhat-lsb-core
    case $(lsb_release -si) in
      Fedora)
        if test $yumdnf = yum; then
          $SUDO $yumdnf install -y yum-utils
        fi
        ;;
      CentOS)
        $SUDO yum install -y yum-utils
        MAJOR_VERSION=$(lsb_release -rs | cut -f1 -d.)
        $SUDO yum-config-manager --add-repo https://dl.fedoraproject.org/pub/epel/$MAJOR_VERSION/x86_64/
        $SUDO yum install --nogpgcheck -y epel-release
        $SUDO rpm --import /etc/pki/rpm-gpg/RPM-GPG-KEY-EPEL-$MAJOR_VERSION
        $SUDO rm -f /etc/yum.repos.d/dl.fedoraproject.org*
        ;;
      *)
        echo "unknown release"
        exit 1
        ;;
    esac

    sed -e 's/@//g' < zlog.spec.in > ${BUILD_DIR}/zlog.spec
    $SUDO $builddepcmd ${BUILD_DIR}/zlog.spec 2>&1 | tee ${BUILD_DIR}/yum-builddep.out
    ! grep -q -i error: ${BUILD_DIR}/yum-builddep.out || exit 1

    # for doc/build.sh
    $SUDO $yumdnf install -y python-virtualenv
    ;;

  *)
    echo "$ID not supported. Install dependencies manually."
    exit 1
    ;;
esac
