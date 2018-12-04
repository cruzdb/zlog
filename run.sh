#!/bin/bash
set -e
set -x

while true; do
for w in 1 2 100; do
  for s in 1 2 100; do
    for z in 0 1 2; do
      for q in 1 8 32; do
        rm -rf /tmp/db
        mkdir /tmp/db
        bin/zlog_bench \
          --backend lmdb \
          --db-path /tmp/db \
          --runtime 10 \
          --verify \
          --width $w \
          --slots $s \
          --size $z \
          --qdepth $q
      done
    done
  done
done
done
