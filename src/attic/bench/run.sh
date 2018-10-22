#!/bin/bash

pool="a"

# for zlog ceph v1 the width will be fixed to something reasonable like num_pgs
# since only a single stripe is created. for zlog ceph v2 we want to create a
# stripe that is large enough to handle all the data for the experiment. this is
# because in the current beta version creating a new stripe interrupts execution
# creating throughput and latency issues.
width=10

#max_entry_size=
#entries_per_object=
#runtime and maxgbs

entry_sizes="10 100 1000"
queue_depths="1 2 4"

for esize in ${entry_sizes}; do
  for qdepth in ${queue_depths}; do
    prefix="es-${esize}.qd-${qdepth}.w-${width}"
    bin/zlog_bench2 --pool ${pool} --width ${width} \
      --size ${esize} --qdepth ${qdepth} \
      --runtime 30 --prefix ${prefix}
  done
done
