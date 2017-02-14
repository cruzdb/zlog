#!/bin/bash

# adapted from https://github.com/ceph/ceph/blob/master/install-deps.sh

set -e

DIR=/tmp/install-deps.$$
trap "rm -fr $DIR" EXIT
mkdir -p $DIR
if test $(id -u) != 0 ; then
  SUDO=sudo
fi

source /etc/os-release
case $ID in
  debian|ubuntu)
    echo "Using apt-get to install dependencies"
    $SUDO apt-get install -y lsb-release devscripts equivs
    $SUDO apt-get install -y dpkg-dev gcc
    if ! test -r debian/control ; then
      echo debian/control is not a readable file
      exit 1
    fi
    touch $DIR/status

    backports=""
    control="debian/control"

    # make a metapackage that expresses the build dependencies,
    # install it, rm the .deb; then uninstall the package as its
    # work is done
    $SUDO env DEBIAN_FRONTEND=noninteractive mk-build-deps --install --remove --tool="apt-get -y --no-install-recommends $backports" $control || exit 1
    $SUDO env DEBIAN_FRONTEND=noninteractive apt-get -y remove cruzdb-build-deps
    if [ -n "$backports" ] ; then rm $control; fi
    ;;

  fedora)

    yumdnf="yum"
    builddepcmd="yum-builddep -y"
    if test "$(echo "$VERSION_ID >= 22" | bc)" -ne 0; then
      yumdnf="dnf"
      builddepcmd="dnf -y builddep --allowerasing"
    fi
    echo "Using $yumdnf to install dependencies"

    $SUDO $yumdnf install -y redhat-lsb-core
    case $(lsb_release -si) in
      Fedora)
        if test $yumdnf = yum; then
          $SUDO $yumdnf install -y yum-utils
        fi
        ;;
      *)
        echo "unknown release"
        exit 1
        ;;
    esac

    #sed -e 's/@//g' < ceph.spec.in > $DIR/ceph.spec
    cp zlog.spec $DIR/zlog.spec
    $SUDO $builddepcmd $DIR/zlog.spec 2>&1 | tee $DIR/yum-builddep.out
    ! grep -q -i error: $DIR/yum-builddep.out || exit 1
    ;;

  *)
    echo "$ID not supported. Install dependencies manually."
    exit 1
    ;;
esac
