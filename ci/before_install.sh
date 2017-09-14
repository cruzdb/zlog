#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

# spin-up a ceph osd
if [[ "${TRAVIS_BRANCH}" != "coverity_scan" ]]; then
if [[ "${TRAVIS_OS_NAME}" == "linux" ]]; then

  # build the zlog ceph-plugin builder image
  pushd ${ZLOG_DIR}/docker/ceph-plugin
  docker build -t ceph-plugin .
  popd

  # build micro-osd docker image
  pushd ${ZLOG_DIR}/docker/micro-osd
  docker build -t micro-osd .
  popd

  # build the zlog ceph plugin from source
  docker run -v /ceph_plugin -v ${ZLOG_DIR}:/src/zlog \
      --name ceph-plugin-built ceph-plugin

  # run the micro-osd with the built plugin
  docker run -d --net=host --volumes-from ceph-plugin-built \
    --name micro-osd -v /tmp/micro-osd:/micro-osd micro-osd

  sleep 10

  docker logs micro-osd
  ls -l /tmp/micro-osd
fi
fi
