#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

# skip ceph tests on osx
if [[ "${TRAVIS_BRANCH}" != "coverity_scan" ]]; then
if [[ "${TRAVIS_OS_NAME}" == "linux" ]]; then
  # build ceph plugin
  docker pull zlog/ceph-plugin || true
  pushd ${ZLOG_DIR}/docker/ceph-plugin
  docker rm built-ceph-plugin || true
  docker build -t ceph-plugin .
  docker run -v /ceph_zlog_plugin --name built-ceph-plugin ceph-plugin
  popd

  # start micro-osd with plugin
  docker pull zlog/micro-osd || true
  pushd ${ZLOG_DIR}/docker/micro-osd
  docker kill micro-osd || true
  docker build -t micro-osd .
  docker run -d --net=host --volumes-from built-ceph-plugin \
    --name micro-osd \
    -v /tmp/micro-osd:/micro-osd micro-osd
  sleep 10 # wait for osd to be up
  popd
fi
fi
