#!/bin/bash
set -e
set -x

ddev=/dev/sdc
jdev=none
pgnum=128
version=jewel
pool=zlog
waitsec=3600
qdepth=16
stripe_width=128
entry_size=1024

exp="map_n1"
interfaces="vanilla cls_no_index cls_no_index_wronly cls_full"
for interface in $interfaces; do
  bench/soft-reset-ceph.sh $ddev $jdev $pool $pgnum $version
  sleep 300
  bench/run-physical-design.sh $pool $exp $stripe_width $entry_size \
    $qdepth $waitsec $interface
done

exp="bytestream_n1_write"
interfaces="vanilla cls_no_index cls_no_index_wronly cls_full"
for interface in $interfaces; do
  bench/soft-reset-ceph.sh $ddev $jdev $pool $pgnum $version
  sleep 300
  bench/run-physical-design.sh $pool $exp $stripe_width $entry_size \
    $qdepth $waitsec $interface
done

exp="bytestream_n1_append"
interfaces="vanilla cls_no_index cls_no_index_wronly cls_check_epoch cls_full"
for interface in $interfaces; do
  bench/soft-reset-ceph.sh $ddev $jdev $pool $pgnum $version
  sleep 300
  bench/run-physical-design.sh $pool $exp $stripe_width $entry_size \
    $qdepth $waitsec $interface
done
