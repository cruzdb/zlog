#!/bin/bash
set -e
set -x

HOST=$1
DDEV=$2
JDEV=$3
PGNUM=128

pool=zlog

# experiment length
waitsec=30

# derive from tuning
qdepth=12
stripe_width=$PGNUM

# we only do fixed size right now
large_entry_size=4096
small_entry_size=128

# names of the experiments to be run
experiments_11="map_11 bytestream_11"
experiments_n1="map_n1 bytestream_n1_write bytestream_n1_append"

# 1:1 workloads use stripe width = 0
for exp in $experiments_11; do
  for entry_size in "$large_entry_size" "$small_entry_size"; do

    # create a unique name for the run
    ename="pool-${pool}_expr-${exp}"
    ename="${ename}_sw-0"
    ename="${ename}_es-${entry_size}"
    ename="${ename}_qd-${qdepth}"
    ename="${ename}.cluster.settings"

    # completely reset ceph (uninstall, install, configure, start)
    bench/reset-ceph.sh $HOST /tmp/${ename} $DDEV $JDEV $pool $PGNUM

    # run the experiment
    bench/run-physical-design.sh $pool $exp 0 $entry_size $qdepth $waitsec

  done
done

# n:1 workloads use stripe width
for exp in $experiments_n1; do
  for entry_size in "$large_entry_size" "$small_entry_size"; do

    # create a unique name for the run
    ename="pool-${pool}_expr-${exp}"
    ename="${ename}_sw-${stripe_width}"
    ename="${ename}_es-${entry_size}"
    ename="${ename}_qd-${qdepth}"
    ename="${ename}.cluster.settings"

    # completely reset ceph (uninstall, install, configure, start)
    bench/reset-ceph.sh $HOST /tmp/${ename} $DDEV $JDEV $pool $PGNUM

    bench/run-physical-design.sh $pool $exp $stripe_width $entry_size $qdepth $waitsec
  done
done
