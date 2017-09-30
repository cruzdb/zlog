#!/bin/bash
#
# Copyright (C) 2015 Red Hat <contact@redhat.com>
#
# Author: Loic Dachary <loic@dachary.org>
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU Library Public License as published by
# the Free Software Foundation; either version 2, or (at your option)
# any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Library Public License for more details.
#
set -e
set -x

./install-deps.sh

git clean -dxf

base=${1:-/tmp/release}
codename=$(lsb_release -sc)
releasedir=${base}/$(lsb_release -si)/WORKDIR

rm -fr $releasedir
mkdir -p $releasedir

vers=$(git describe --match "v*" | sed s/^v//)
./make-dist.sh $vers

# rename to deb conventions
mv zlog-$vers.tar.bz2 $releasedir/zlog_$vers.orig.tar.bz2
tar -C $releasedir -jxf $releasedir/zlog_$vers.orig.tar.bz2

# this is useful when hacking on debian scripts. otherwise the build will only
# consider what is committed in git.
#cp -a debian/* $releasedir/zlog-$vers/debian/

cd ${releasedir}/zlog-${vers}
dpkg-buildpackage -j$(nproc) -uc -us
