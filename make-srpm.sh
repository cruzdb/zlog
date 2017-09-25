#!/bin/bash
set -e
set -x

root=fedora-25-x86_64
short=fc25

[ -z "$version" ] && version=`git describe --match 'v*' | sed 's/^v//'`

if expr index ${version} '-' > /dev/null; then
	rpm_version=`echo ${version} | cut -d - -f 1-1`
	rpm_release=`echo ${version} | cut -d - -f 2- | sed 's/-/./'`
else
	rpm_version=${version}
	rpm_release=0
fi

version=${rpm_version}-${rpm_release}
./make-dist.sh $version

bdir=$(mktemp -d)
mkdir -p ${bdir}/SPECS
mkdir -p ${bdir}/SOURCES
mkdir -p ${bdir}/SRPMS
mkdir -p ${bdir}/RPMS

cp zlog.spec ${bdir}/SPECS/
mv zlog-${version}.tar.bz2 ${bdir}/SOURCES/


mock --buildsrpm \
  --root ${root} \
  --spec ${bdir}/SPECS/zlog.spec \
  --sources ${bdir}/SOURCES/zlog-${version}.tar.bz2 \
  --resultdir ${bdir}/SRPMS

mock --root ${root} \
  --resultdir ${bdir}/RPMS \
  --rebuild \
  ${bdir}/SRPMS/zlog-${version}.${short}.src.rpm

ls -lR ${bdir}
