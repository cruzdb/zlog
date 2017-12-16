#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../

DOCS_DIR=$(mktemp -d)
trap "rm -rf ${DOCS_DIR}" EXIT

${ZLOG_DIR}/doc/build.sh ${DOCS_DIR}
test -r ${DOCS_DIR}/output/html/index.html

pushd ${DOCS_DIR}/output/html
test ! -e .git
git init .
touch .nojekyll # skip jekyll processing
git add .
git commit -m "published"

git remote add origin git@github.com:cruzdb/zlog.git
git push -f origin master:gh-pages
popd
