#!/bin/bash
# adapted from https://github.com/ceph/ceph/blob/master/admin/build-doc

cd "$(dirname "$0")"
cd ..
TOPDIR=`pwd`

for package in python-devel python-pip python2-virtualenv; do
  if ! rpm -q $package >/dev/null ; then
    missing="${missing:+$missing }$package"
  fi
done

if [ -n "$missing" ]; then
  echo "$0: missing required packages, please install them:" 1>&2
  echo "yum/dnf install -y $missing"
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
