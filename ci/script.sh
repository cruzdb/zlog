#!/bin/bash

set -e
set -x

COVERAGE_ENV=""
if [ "${RUN_COVERAGE}" == 1 ]; then
  COVERAGE_ENV=`bash <(curl -s https://codecov.io/env)`
fi

if [ ! -z ${DOCKER_IMAGE+x} ]; then
  docker run --net=host --rm -v ${TRAVIS_BUILD_DIR}:/zlog:z,ro \
    -w /zlog ${COVERAGE_ENV} -e RUN_COVERAGE \
    -v /tmp/micro-osd:/tmp/micro-osd:z ${DOCKER_IMAGE} \
    /bin/bash -c "env && ./install-deps.sh && ./ci/install-ceph.sh && ./ci/run.sh"
else
  ${TRAVIS_BUILD_DIR}/install-deps.sh
  ${TRAVIS_BUILD_DIR}/ci/install-ceph.sh
  ${TRAVIS_BUILD_DIR}/ci/run.sh
fi
