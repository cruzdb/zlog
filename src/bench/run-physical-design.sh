#!/bin/bash

set -x
set -e

pool=$1
experiment=$2
stripe_width=$3
entry_size=$4
qdepth=$5
waitsec=$6

perf_file="pool-${pool}_expr-${experiment}"
perf_file="${perf_file}_sw-${stripe_width}"
perf_file="${perf_file}_es-${entry_size}"
perf_file="${perf_file}_qd-${qdepth}"
perf_file="${perf_file}.log"

args="--pool $pool"
args="$args --experiment $experiment"
args="$args --stripe_width $stripe_width"
args="$args --entry_size $entry_size"
args="$args --qdepth $qdepth"
args="$args --perf_file $perf_file"
args="$args --prefix pre1"

echo "Running: ./physical-design $args"
./physical-design $args &
pid=$!

echo "Waiting: $waitsec seconds"
sleep $waitsec
echo "Kill: $pid"
kill -INT $pid
echo "Wait: on $pid"
wait $pid
