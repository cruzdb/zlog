#!/bin/bash

set -e
set -x

pushd /src/zlog
cmake .
make cls_zlog
