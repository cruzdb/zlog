#!/bin/bash
# adapted from https://github.com/ceph/ceph/blob/master/admin/build-doc

set -e

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../
OUTPUT_DIR=${1:-"${ZLOG_DIR}/build-doc"}

for command in virtualenv; do
  command -v "$command" > /dev/null;
  ret_code=$?
  if [ $ret_code -ne 0 ]; then
    missing="${missing:+$missing }$command"
  fi
done
if [ -n "$missing" ]; then
  echo "$0: missing required command, please install them:" 1>&2
  echo "$missing"
  exit 1
fi

mkdir -p ${OUTPUT_DIR}
if [ ! -e ${OUTPUT_DIR}/virtualenv ]; then
  virtualenv --no-site-packages ${OUTPUT_DIR}/virtualenv
  ${OUTPUT_DIR}/virtualenv/bin/pip install -U pip
fi

${OUTPUT_DIR}/virtualenv/bin/pip install --quiet \
  -r ${ZLOG_DIR}/doc/requirements.txt

mkdir -p ${OUTPUT_DIR}/output/html
${OUTPUT_DIR}/virtualenv/bin/sphinx-build -W -a -n -b dirhtml \
  -d ${OUTPUT_DIR}/doctrees ${ZLOG_DIR}/doc ${OUTPUT_DIR}/output/html
