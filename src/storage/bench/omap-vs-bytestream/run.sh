#!/bin/bash
set -e
set -x

backend=ceph
pool=zlog
runtime=5

for size in 1 128 1024 4096 4097 8192 8193 16384 16385; do

  prefix="$(date +%s).${size}.omap"

  bin/zlog_backend_bench \
    --backend ${backend} \
    --pool ${pool} \
    --qdepth 32 \
    --runtime ${runtime} \
    --width 128 \
    --slots 4096 \
    --size ${size} \
    --prefix ${prefix} \
    --maxpos 2000000 > ${prefix}.log

  prefix="$(date +%s).${size}.bytestream"

  bin/zlog_backend_bench \
    --backend ${backend} \
    --pool ${pool} \
    --qdepth 32 \
    --runtime ${runtime} \
    --width 128 \
    --slots 4096 \
    --size ${size} \
    --prefix ${prefix} \
    --maxpos 2000000 \
    --bytestream > ${prefix}.log

done
