#!/bin/sh
set -e
set -x

rm -rf ./alpine/zlog

./make-dist.sh
mv -f *.tar.bz2 ./alpine

rm -rf .abuild
mkdir -p .abuild
ABUILD_USERDIR=$(pwd)/.abuild abuild-keygen -n -a
source .abuild/abuild.conf

cd alpine
abuild checksum && JOBS=$(expr $(nproc) / 2) SRCDEST=$(pwd) REPODEST=$(pwd) PACKAGER_PRIVKEY=$PACKAGER_PRIVKEY abuild -r
cd ..
