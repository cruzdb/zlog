#!/bin/bash

set -e

name=tpsweep
runtime=300
pg_nums="32 128"
stripe_widths="32 128"
queue_depths="1 8 16 32"
entry_sizes="512"
pool=zlog
rest=120

# workloads and i/o interfaces
workloads="bytestream_n1_append"
bytestream_n1_append_if="vanilla"

. run.sh
run_pd
