#!/bin/bash

set -x
set -e

pool=$1
experiment=$2
stripe_width=$3
entry_size=$4
qdepth=$5
waitsec=$6
interface=$7
#prefix=$8

perf_file="pool-${pool}_expr-${experiment}"
perf_file="${perf_file}_sw-${stripe_width}"
perf_file="${perf_file}_es-${entry_size}"
perf_file="${perf_file}_qd-${qdepth}"
perf_file="${perf_file}_rt-${waitsec}"
perf_file="${perf_file}_if-${interface}"
perf_file="${perf_file}.log"

args="--pool $pool"
args="$args --experiment $experiment"
args="$args --stripe_width $stripe_width"
args="$args --entry_size $entry_size"
args="$args --qdepth $qdepth"
args="$args --tp 2"
args="$args --perf_file $perf_file"
args="$args --runtime $waitsec"
args="$args --interface $interface"
#args="$args --prefix $prefix"

echo "Running: ./physical-design $args"
./physical-design $args
