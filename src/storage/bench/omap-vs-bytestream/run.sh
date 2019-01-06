#!/bin/bash
set -e
set -x

backend=ceph
pool=zlog
runtime=120

# always omap, always bytestream, bytestream >= 4096
for omap_max_size in 200000 0 4096; do
for size in 1 128 1024 4096 4097 8192 8193 16384 16385 131072 131073; do

  prefix="$(date +%s).${size}.${omap_max_size}"
  slots=$((128 * 1048576 / ${size}))
  if [ ${slots} -gt 32768 ]; then
    slots=32768
  fi

  bin/zlog_backend_bench \
    --backend ${backend} \
    --pool ${pool} \
    --qdepth 32 \
    --runtime ${runtime} \
    --width 128 \
    --slots ${slots} \
    --size ${size} \
    --prefix ${prefix} \
    --maxpos 5000000 \
    --omap-max-size ${omap_max_size} > ${prefix}.log

  sleep 120

done
done
