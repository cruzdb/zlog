#!/bin/bash

set -e
set -x

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZLOG_DIR=${THIS_DIR}/../../../

: ${PREFIX:="result"}
: ${NUM_THREADS:=1}
: ${YCSB_HOME:=$HOME/YCSB}
: ${LMDB_PATH:=${THIS_DIR}/db}

function resetdb {
  rm -rf ${LMDB_PATH}
  mkdir ${LMDB_PATH}
}

export LD_LIBRARY_PATH=${ZLOG_DIR}/src/java/native
export ZLOG_LMDB_BE_SIZE=100

for nthreads in $NUM_THREADS; do
  resultdir=${THIS_DIR}/${PREFIX}.${nthreads}_threads
  mkdir $resultdir

  pushd ${YCSB_HOME}
  for workload in a b c d e f; do
    resetdb

    name="workload_${workload}"

    # only one thread used for load
    bin/ycsb load cruzdb -s \
      -P workloads/workload${workload} \
      -P ${THIS_DIR}/big.conf \
      -p cruzdb.lmdb.dir=${LMDB_PATH} 2>&1 | tee ${resultdir}/${name}.load.txt

    bin/ycsb run cruzdb -threads ${nthreads} -s \
      -P workloads/workload${workload} \
      -P ${THIS_DIR}/big.conf \
      -p cruzdb.lmdb.dir=${LMDB_PATH} 2>&1 | tee ${resultdir}/${name}.run.txt
  done
  popd
done
