#!/bin/bash

set -e

if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
  #
  # Build and cache the ZLog plugin for Ceph?
  #
  if [ ! -f "$HOME/zlog_ceph_deps/cls_zlog_client.h" ]; then
    #
    # The plugin is built in a docker image
    #
cat <<EOF | docker build -t zlog_deps -
FROM ubuntu:trusty

RUN apt-get update -qq && apt-get install -y git build-essential

RUN mkdir -p /src/ceph && cd /src/ceph && \
    git clone --recursive --branch=zlog/jewel \
      https://github.com/noahdesu/ceph.git && \
    cd ceph && ./install-deps.sh

RUN cd /src/ceph/ceph && ./autogen.sh && \
    ./configure --prefix=/usr && \
    cd src && make libcls_zlog.la libcls_zlog_client.la
EOF
    # copy artificats back into host
    mkdir -p $HOME/zlog_ceph_deps
    docker run -v $HOME/zlog_ceph_deps/:/deps -it zlog_deps \
      bash -c "cp -a /src/ceph/ceph/src/.libs/libcls_zlog.so* /deps"
    docker run -v $HOME/zlog_ceph_deps/:/deps -it zlog_deps \
      bash -c "cp -a /src/ceph/ceph/src/.libs/libcls_zlog_client.so* /deps"
    docker run -v $HOME/zlog_ceph_deps/:/deps -it zlog_deps \
      cp /src/ceph/ceph/src/cls/zlog/cls_zlog_client.h /deps
  fi

  # install (either from cache, or just built in docker above)
  sudo ls -l $HOME/zlog_ceph_deps/
  sudo cp -a $HOME/zlog_ceph_deps/libcls_zlog.so* /usr/lib/rados-classes/
  sudo cp -a $HOME/zlog_ceph_deps/libcls_zlog_client.so* /usr/lib/
  sudo cp $HOME/zlog_ceph_deps/cls_zlog_client.h /usr/include/rados/

  # start ceph
  ci/micro-osd.sh /tmp/osd
  CEPH_CONF=/tmp/osd/ceph.conf ceph status
fi

mkdir build
pushd build

if [ "${RUN_COVERAGE}" == 1 ]; then
  cmake -DCMAKE_BUILD_TYPE=Coverage ..
else
  cmake -DCMAKE_BUILD_TYPE=Debug ..
fi

make -j2
./src/test/zlog-test-ram
./src/test/db-test

# on linux we assume a ceph instance is running and execute any tests that
# depend on the ceph backend being available.
if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
  CEPH_CONF=/tmp/osd/ceph.conf ./src/zlog-seqr --streams --port 5678 --daemon
  CEPH_CONF=/tmp/osd/ceph.conf ./src/test/zlog-test-ceph
fi

if [ "${RUN_COVERAGE}" == 1 ]; then
  make db-test-cov
  make zlog-test-ram-cov
  if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
    CEPH_CONF=/tmp/osd/ceph.conf make zlog-test-ceph-cov
  fi
fi

popd
