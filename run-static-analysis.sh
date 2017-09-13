#!/bin/bash
set -e

## cppcheck
## add "--check-config" to check for missing includes
#docker run --rm -it -v $PWD:/zlog:z,ro -w /zlog cppcheck cppcheck \
#  --force \
#  --inconclusive \
#  --enable=all \
#  --std=c++11 \
#  --quiet \
#  -I/zlog/build/src \
#  -I/zlog/src \
#  -I/zlog/src/include \
#  -I/zlog/src/spdlog/include \
#  -I/zlog/src/rapidjson/include \
#  -i/zlog/build \
#  -i/zlog/src/spdlog \
#  -i/zlog/src/rapidjson \
#  -i/zlog/src/googletest \
#  -i/zlog/src/kvstore/persistent-rbtree.cc \
#  /zlog | tee cppcheck.txt
#
## include-what-you-use
#docker run --rm -it -v $PWD:$PWD:z,ro -w $PWD iwyu \
#  /usr/src/iwyu/iwyu_tool.py -p build | tee iwyu.txt

# scan-build
rm -rf scan-build-results
mkdir scan-build-results
docker run --rm -it -v $PWD:/zlog:z,ro \
  -v $PWD/scan-build-results:/results:z scan-build \
  /bin/bash -c "\
    cd /zlog && \
    ./install-deps.sh && ci/install-ceph.sh && \
    mkdir /build && cd /build && \
    scan-build-4.0 cmake /zlog &&
    scan-build-4.0 -o /results make -j4"
