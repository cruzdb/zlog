#!/bin/bash
set -e
set -x

pool=zlog
waitsec=30
qdepth=12
stripe_width=10
entry_size=100

exp="map_n1"
interfaces="vanilla cls_no_index cls_full"
for interface in $interfaces; do
  bench/run-physical-design.sh $pool $exp $stripe_width $entry_size \
    $qdepth $waitsec $interface
done

exp="bytestream_n1_write"
interfaces="vanilla cls_no_index cls_full"
for interface in $interfaces; do
  bench/run-physical-design.sh $pool $exp $stripe_width $entry_size \
    $qdepth $waitsec $interface
done

exp="bytestream_n1_append"
interfaces="vanilla cls_no_index cls_check_epoch cls_full"
for interface in $interfaces; do
  bench/run-physical-design.sh $pool $exp $stripe_width $entry_size \
    $qdepth $waitsec $interface
done
