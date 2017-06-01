#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

# TODO: add cls plugin to coverity
if [[ "${TRAVIS_BRANCH}" != "coverity_scan" ]]; then
if [[ "${TRAVIS_OS_NAME}" == "linux" ]]; then

  pushd ${ZLOG_DIR}/docker/ceph-plugin
  docker build -t ceph-plugin .
  popd

  pushd ${ZLOG_DIR}/docker/micro-osd
  docker build -t micro-osd .
  popd

  docker run -v /ceph_plugin -v ${ZLOG_DIR}:/src/zlog \
      --name ceph-plugin-built ceph-plugin

  docker run -d --net=host --volumes-from ceph-plugin-built \
    --name micro-osd -v /tmp/micro-osd:/micro-osd micro-osd

  sleep 10
fi
fi
