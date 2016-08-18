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
