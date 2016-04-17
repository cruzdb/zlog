#!/bin/bash

set -e

# name of results dir
logdir=$PWD/results.pd.${name}.$(hostname --short).$(date +"%m-%d-%Y_%H-%M-%S")
mkdir $logdir

function run_pd() {

# log file dir in container
guest_logdir=/results

for pgnum in $pg_nums; do
for stripe_width_want in $stripe_widths; do
for qdepth in $queue_depths; do
for entry_size in $entry_sizes; do
for workload in $workloads; do

if [ "$workload" = "map_n1" ]; then
  interfaces=$map_n1_if
elif [ "$workload" = "bytestream_n1_write" ]; then
  interfaces=$bytestream_n1_write_if
elif [ "$workload" = "bytestream_n1_append" ]; then
  interfaces=$bytestream_n1_append_if
else
  interfaces="vanilla"
fi

for interface in $interfaces; do

if [ "$workload" = "map_11" ] || [ "$workload" = "bytestream_11" ]; then
  stripe_width=0
else
  stripe_width=$stripe_width_want
fi

ename="pool-${pool}_expr-${workload}"
ename="${ename}_sw-${stripe_width}"
ename="${ename}_es-${entry_size}"
ename="${ename}_qd-${qdepth}"
ename="${ename}_pg-${pgnum}"
ename="${ename}_rt-${runtime}"
ename="${ename}_if-${interface}"

set -x

docker run --net=host \
  -v $logdir:$guest_logdir \
  -v /etc/ceph:/etc/ceph \
  -it zlog-pd \
  --pool $pool \
  --pgnum $pgnum \
  --workload $workload \
  --stripe-width $stripe_width \
  --entry-size $entry_size \
  --queue-depth $qdepth \
  --runtime $runtime \
  --interface $interface \
  --output $guest_logdir/$ename \
  --rest $rest

set +x

done
done
done
done
done
done

}
