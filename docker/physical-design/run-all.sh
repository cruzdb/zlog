#!/bin/bash

name=all

runtime=10
pg_nums="128"
stripe_widths="5"
queue_depths="4"
entry_sizes="4096"
pool=zlog
name=tp_sweep

# workloads
wl_11="map_11 bytestream_11"
wl_n1="map_n1 bytestream_n1_write bytestream_n1_append"
workloads="$wl_11 $wl_n1"

# i/o interfaces
map_n1_if="vanilla cls_no_index cls_no_index_wronly cls_full"
bytestream_n1_write_if="vanilla cls_no_index cls_no_index_wronly cls_full cls_full_hdr_idx cls_full_inline_idx"
bytestream_n1_append_if="vanilla cls_no_index cls_no_index_wronly cls_check_epoch cls_check_epoch_hdr cls_full cls_full_hdr_idx cls_no_index_wronly_xtn"

. run.sh
run_pd
