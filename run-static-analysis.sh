#!/bin/bash

set -e
set -x

sudo docker run -v $PWD:/home/nwatkins/src/zlog:z -w /home/nwatkins/src/zlog -it
iwyu /usr/src/iwyu/iwyu_tool.py -p .

# see github.com/noahdesu/docks/cppcheck
docker run --rm -i -v $PWD:/usr/src/zlog:ro cppcheck \
  cppcheck --force --inconclusive --enable=all /usr/src/zlog \
  -i/usr/src/zlog/src/spdlog -i/usr/src/zlog/src/rapidjson \
  -i/usr/src/zlog/src/googletest

#docker run --rm -v $PWD:/usr/src/zlog:ro iwyu \
#  /bin/bash -c "/usr/src/zlog/install-deps.sh && mkdir /build && cd /build && \
#    echo $CC $CXX && cmake -DCMAKE_CXX_INCLUDE_WHAT_YOU_USE=/usr/src/iwyu /usr/src/zlog && \
#    make"
