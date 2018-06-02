#!/bin/bash

pool="javier"

width=1000
entries_per_object="1024"
runtime="12"
entry_sizes="100 1000"
queue_depths="2 4"
cache_size="0 1024 65536"
cache_eviction="0 1"
backend="ceph"

#export ZLOG_LMDB_BE_SIZE=20

scanv=""

if [ "$1" != "scan" ] ; then
  #rm -rf /tmp/zlog.tmp.db
  #mkdir /tmp/zlog.tmp.db
  #./bin/create_log_lmdb
else
  scanv="--scan"
fi



for esize in ${entry_sizes}; do
  for qdepth in ${queue_depths}; do
    for csize in ${cache_size}; do
      for cevic in ${cache_eviction}; do
        prefix="es-${esize}.qd-${qdepth}.w-${width}.cs-${csize}.ep-${cevic}"
        bin/zlog_cache_bench --pool ${pool} --width ${width} \
          --size ${esize} --qdepth ${qdepth} \
          --runtime ${runtime} --prefix ${prefix} \
          --cache_size ${csize} --cache_eviction ${cevic} \
          --epo ${entries_per_object} --backend ${backend} --logname ${prefix} \
          --max_gbs 5 ${scanv}
      done
    done
  done
done
