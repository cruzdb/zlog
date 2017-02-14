#!/bin/bash
# adapted from https://github.com/ceph/ceph/blob/master/admin/build-doc

cd "$(dirname "$0")"
cd ..
TOPDIR=`pwd`

if command -v dpkg > /dev/null; then
  for package in python-dev python-pip python-virtualenv; do
    if [ "$(dpkg --status -- $package 2>&1 | sed -n 's/^Status: //p')" != "install ok installed" ]; then
        missing="${missing:+$missing }$package"
    fi
  done
  if [ -n "$missing" ]; then
    echo "$0: missing required packages, please install them:" 1>&2
    echo "sudo apt-get install -o APT::Install-Recommends=true $missing" 1>&2
    exit 1
  fi
elif command -v yum > /dev/null; then
  for package in python-devel python-pip python2-virtualenv; do
    if ! rpm -q $package >/dev/null ; then
      missing="${missing:+$missing }$package"
    fi
  done
  if [ -n "$missing" ]; then
    echo "$0: missing required packages, please install them:" 1>&2
    echo "yum install -y $missing"
    exit 1
  fi
fi

for command in virtualenv; do
  command -v "$command" > /dev/null;
  ret_code=$?
  if [ $ret_code -ne 0 ]; then
    missing="${missing:+$missing }$command"
  fi
done
if [ -n "$missing" ]; then
  echo "$0: missing required command, please install them:" 1>&2
  echo "$missing"
  exit 1
fi

set -e

mkdir build-doc || true
cd build-doc

[ -z "$vdir" ] && vdir="$TOPDIR/build-doc/virtualenv"
if [ ! -e $vdir ]; then
    virtualenv --system-site-packages $vdir
fi
$vdir/bin/pip install --quiet -r $TOPDIR/doc/requirements.txt

mkdir -p $TOPDIR/build-doc/output/html

$vdir/bin/sphinx-build -a -n -b dirhtml -d doctrees \
  $TOPDIR/doc $TOPDIR/build-doc/output/html
