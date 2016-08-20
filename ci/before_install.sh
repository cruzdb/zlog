#!/bin/bash

set -e

if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
  curl https://download.ceph.com/keys/release.asc | sudo apt-key add -
  sudo apt-add-repository 'deb https://download.ceph.com/debian-jewel/ trusty main'
  sudo apt-get update -qq
  sudo apt-get install -y ceph librados-dev
  sudo pip install cpp-coveralls

elif [ "${TRAVIS_OS_NAME}" == "osx" ]; then
  brew update
  brew install boost protobuf cmake || true
fi

#
# Build and cache the ZLog plugin for Ceph? If the cache is empty we'll build
# the plugin inside a docker container and move the plugin into the cache.
#
if [ "${TRAVIS_OS_NAME}" == "linux" ]; then
  if [ ! -f "$HOME/zlog_ceph_deps/cls_zlog_client.h" ]; then

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
fi
