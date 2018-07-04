#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

export TRAVIS_BRANCH=
export TRAVIS_OS_NAME="linux"
export DOCKER_IMAGE=ubuntu:bionic
export TRAVIS_BUILD_DIR=${ZLOG_DIR}

trap "docker kill micro-osd ceph-plugin-built; docker rm micro-osd ceph-plugin-built" EXIT

ci/before_install.sh
ci/script.sh
