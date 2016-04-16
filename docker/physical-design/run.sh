#!/bin/bash

set -x -e

runtime=30
logdir=/tmp/
pg_nums="128"
stripe_widths="4"
queue_depths="4"
entry_sizes="4096"

pool=zlog

# workloads
wl_11="map_11 bytestream_11"
wl_n1="map_n1 bytestream_n1_write bytestream_n1_append"
workloads="$wl_n1"

# log file dir in container
guest_logdir=/results

# is there another interface for when we verified the extra write won't hurt
# anything (for the txn?)

#ddev=/dev/sdc
#jdev=none
#pgnum=128
#version=jewel
#pool=zlog
#waitsec=3600
#qdepth=16
#stripe_width=128
#entry_size=1024

#exp="map_n1"
#interfaces="vanilla cls_no_index cls_no_index_wronly cls_full"
#interfaces="vanilla cls_no_index cls_no_index_wronly cls_full"
#
#exp="bytestream_n1_write"
#interfaces="vanilla cls_no_index cls_no_index_wronly cls_full cls_full_hdr_idx cls_full_inline_idx"
#interfaces="vanilla cls_no_index cls_no_index_wronly cls_full cls_full_hdr_idx cls_full_inline_idx"
#
#exp="bytestream_n1_append"
#interfaces="vanilla cls_no_index cls_no_index_wronly cls_check_epoch cls_check_epoch_hdr cls_full cls_full_hdr_idx"
#interfaces="vanilla cls_no_index cls_no_index_wronly cls_check_epoch cls_check_epoch_hdr cls_full cls_full_hdr_idx"
#
## extras

# interfaces
# workloads
# etc ceph
# extra

for pgnum in $pg_nums; do
for stripe_width in $stripe_widths; do
for qdepth in $queue_depths; do
for entry_size in $entry_sizes; do
for workload in $workloads; do

interface=vanilla

ename="pool-${pool}_expr-${workload}"
ename="${ename}_sw-${stripe_width}"
ename="${ename}_es-${entry_size}"
ename="${ename}_qd-${qdepth}"
ename="${ename}_rt-${runtime}"
ename="${ename}_if-${interface}"

docker run --net=host \
  -v $logdir:$guest_logdir \
  -v $HOME/src/ceph/src/ceph.conf:/etc/ceph/ceph.conf \
  -v /home/nwatkins/src/ceph/src/:/home/nwatkins/src/ceph/src/ \
  -it zlog \
  --pool $pool \
  --pgnum $pgnum \
  --workload $workload \
  --stripe-width $stripe_width \
  --entry-size $entry_size \
  --queue-depth $qdepth \
  --runtime $runtime \
  --interface $interface \
  --output $guest_logdir/$ename

done
done
done
done
done
