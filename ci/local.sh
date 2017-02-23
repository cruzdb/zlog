#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

export TRAVIS_BRANCH=
export TRAVIS_OS_NAME="linux"
export DOCKER_IMAGE=ubuntu:xenial
export TRAVIS_BUILD_DIR=${ZLOG_DIR}

ci/before_install.sh
ci/script.sh

docker kill micro-osd || true
