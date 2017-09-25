#!/bin/bash
set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../../
RESULTS_DIR=${PWD}/sa_results

rm -rf ${RESULTS_DIR}
mkdir ${RESULTS_DIR}

docker run --rm -it \
  -v ${ZLOG_DIR}:/src/zlog:z,ro \
  -v ${RESULTS_DIR}:/results:z \
  -w /src/zlog \
  zlog/static-analysis
