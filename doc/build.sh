#!/bin/bash
# adapted from https://github.com/ceph/ceph/blob/master/admin/build-doc
set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../
OUTPUT_DIR=${1:-"${ZLOG_DIR}/build-doc"}

mkdir -p ${OUTPUT_DIR}
if [ ! -e ${OUTPUT_DIR}/virtualenv ]; then
  set +e
  virtualenv ${OUTPUT_DIR}/virtualenv
  if [ $? -ne 0 ]; then
    set -e
    python3 -m venv ${OUTPUT_DIR}/virtualenv
  fi
  set -e
  ${OUTPUT_DIR}/virtualenv/bin/pip install -U pip
fi

${OUTPUT_DIR}/virtualenv/bin/pip install --quiet \
  -r ${ZLOG_DIR}/doc/requirements.txt

mkdir -p ${OUTPUT_DIR}/output/html
${OUTPUT_DIR}/virtualenv/bin/sphinx-build -W -a -n -b dirhtml \
  -d ${OUTPUT_DIR}/doctrees ${ZLOG_DIR}/doc ${OUTPUT_DIR}/output/html

BUILD_DIR=$(mktemp -d)
trap "rm -rf ${BUILD_DIR}" EXIT

pushd ${BUILD_DIR}
cmake -DWITH_JNI=ON ${ZLOG_DIR}
make zlog_javadoc
popd

JAVADOC_OUTDIR=${OUTPUT_DIR}/output/html/api/java
mkdir -p ${JAVADOC_OUTDIR}
cp -a ${BUILD_DIR}/src/java/javadoc/zlog/* ${JAVADOC_OUTDIR}
rm -rf ${BUILD_DIR}
