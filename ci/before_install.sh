#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

# skip ceph tests on osx
if [[ "${TRAVIS_BRANCH}" != "coverity_scan" ]]; then
if [[ "${TRAVIS_OS_NAME}" == "linux" ]]; then
  # build ceph plugin
  pushd ${ZLOG_DIR}/docker/ceph-plugin
  docker rm built-ceph-plugin || true
  docker pull zlog/ceph-plugin:latest || true
  if [[ "$(docker images -q zlog/ceph-plugin:latest 2> /dev/null)" == "" ]]; then
    docker build -t zlog/ceph-plugin:latest .
  fi
  docker run -v /ceph_zlog_plugin --name built-ceph-plugin zlog/ceph-plugin:latest
  popd

  pushd ${ZLOG_DIR}/docker/micro-osd
  docker kill micro-osd || true
  docker pull zlog/micro-osd:latest || true
  if [[ "$(docker images -q zlog/micro-osd:latest 2> /dev/null)" == "" ]]; then
    docker build -t zlog/micro-osd:latest .
  fi
  docker run -d --net=host --volumes-from built-ceph-plugin \
    --name micro-osd \
    -v /tmp/micro-osd:/micro-osd zlog/micro-osd:latest
  sleep 10 # wait for osd to be up
  popd
fi
fi
