#!/bin/bash

set -x -e

runtime=30
logdir=/tmp/
pg_nums="128"
stripe_widths="5"
queue_depths="4"
entry_sizes="4096"
pool=zlog

# workloads
wl_11="map_11 bytestream_11"
wl_n1="map_n1 bytestream_n1_write bytestream_n1_append"
workloads="$wl_11 $wl_n1"

# i/o interfaces
map_n1_if="vanilla cls_no_index cls_no_index_wronly cls_full"
bytestream_n1_write_if="vanilla cls_no_index cls_no_index_wronly cls_full cls_full_hdr_idx cls_full_inline_idx"
bytestream_n1_append_if="vanilla cls_no_index cls_no_index_wronly cls_check_epoch cls_check_epoch_hdr cls_full cls_full_hdr_idx cls_no_index_wronly_xtn"

# log file dir in container
guest_logdir=/results

for pgnum in $pg_nums; do
for stripe_width in $stripe_widths; do
for qdepth in $queue_depths; do
for entry_size in $entry_sizes; do
for workload in $workloads; do

if [ "$workload" = "map_n1" ]; then
  interfaces=$map_n1_if
else if [ "$workload" = "bytestream_n1_write" ]; then
  interfaces=$bytestream_n1_write_if
else if [ "$workload" = "bytestream_n1_append" ]; then
  interfaces=$bytestream_n1_append_if
else
  interfaces="vanilla"
fi

for interface in $interfaces; do

if [ "$workload" = "map_11" || "$workload" = "bytestream_11" ]; then
  stripe_width=0
fi

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
done
