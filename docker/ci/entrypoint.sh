#!/bin/bash
set -e
set -x

# checkout zlog
if [ ! -d /src/zlog ]; then
  BRANCH=${branch:-master}
  git clone --branch=$BRANCH https://github.com/cruzdb/zlog.git /src/zlog
fi

bash /src/zlog/docker/ci/run.sh
