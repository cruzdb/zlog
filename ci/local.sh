#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

export TRAVIS_BRANCH=
export TRAVIS_OS_NAME="linux"
export DOCKER_IMAGE=ubuntu:xenial
export TRAVIS_BUILD_DIR=${ZLOG_DIR}

trap "docker kill micro-osd; docker rm micro-osd" EXIT

ci/before_install.sh
ci/script.sh
