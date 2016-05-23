#!/bin/bash
set -e

#
# Example script
#
# name=all
# runtime=10
# pg_nums="128"
# stripe_widths="5"
# queue_depths="4"
# entry_sizes="4096"
# pool=zlog
#
# # workloads
# wl_11="map_11 bytestream_11"
# wl_n1="map_n1 bytestream_n1_write bytestream_n1_append"
# workloads="$wl_11 $wl_n1"
#
# # i/o interfaces
# map_n1_if="vanilla cls_no_index cls_no_index_wronly cls_full"
# bytestream_n1_write_if="vanilla cls_no_index cls_no_index_wronly cls_full cls_full_hdr_idx cls_full_inline_idx"
# bytestream_n1_append_if="vanilla cls_no_index cls_no_index_wronly cls_check_epoch cls_check_epoch_hdr cls_full cls_full_hdr_idx cls_no_index_wronly_xtn"
#
# . runner.sh
# run_pd
#

#if [ "x$reads" = "xyes" ]; then
#  if [ "$(whoami)" != "root" ]; then
#    echo "root needed for reads to drop caches"
#    exit 1
#  fi
#fi

# name of results dir
logdir=$PWD/results.pd.${name}.$(hostname --short).$(date +"%m-%d-%Y_%H-%M-%S")
mkdir $logdir

this_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

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
ename="${ename}_ms-0"

set -x

# if reset is set to 'soft' then we will nuke the ceph installation before
# proceeding. in either case the experiment will ensure it is using a fresh
# pool configured according to the experiment parameters.
if [ "x$reset" = "xsoft" ]; then
  if [ -z ${noop_dev+x} ]; then
    noop_dev_opt=""
  else
    noop_dev_opt="--noop ${noop_dev}"
  fi

  if [ -z ${journal_dev+x} ]; then
    journal_dev_opt=""
  else
    journal_dev_opt="--journal-dev ${journal_dev}"
  fi

  if [ -z ${bluestore+x} ]; then
    bluestore=""
  else
    bluestore="--bluestore true"
  fi

  if [ -z ${ceph_version+x} ]; then
    ${this_dir}/single-node-ceph.sh --data-dev ${data_dev} ${journal_dev_opt} ${noop_dev_opt} ${bluestore}
  else
    ${this_dir}/single-node-ceph.sh --data-dev ${data_dev} ${journal_dev_opt} ${noop_dev_opt} ${bluestore} --version ${ceph_version}
  fi
fi

set +x

cat /sys/fs/cgroup/blkio/blkio.throttle.write_iops_device || true
cat /sys/fs/cgroup/blkio/blkio.throttle.read_iops_device || true

#
# This is always a write workload
#
maxseq_tmpfile=`mktemp`
stdbuf -oL docker run --net=host \
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
  --rest $rest | { while IFS= read -r line
do
  if [[ $line =~ maxseq\ ([0-9]+) ]]; then
    maxseq=${BASH_REMATCH[1]}
  fi
  echo $line
done
echo $maxseq > $maxseq_tmpfile
}

maxseq=$(cat $maxseq_tmpfile)
rm $maxseq_tmpfile

if ! [[ $maxseq =~ ^[0-9]+$ ]]; then
  echo "maxseq is not a number / not found"
  exit 1
fi

set -x

#
# If we have requested a read workload we should do that now after we have
# filled up the osd. The setup is currently very simple: if reads are
# requested then we run the same read workload for each write experiment that
# supports it.
#
read_expr="dne"
if [ "x$reads" = "xyes" ]; then

  if [ "$workload" = "map_11" ]; then
    read_expr="map_11_read"
  elif [ "$workload" = "bytestream_11" ]; then
    read_expr="bytestream_11_read"
  elif [ "$workload" = "map_n1" ]; then
    read_expr="map_n1_read"
  elif [ "$workload" = "bytestream_n1_write" ]; then
    read_expr="bytestream_n1_read"
  else
    if [ "$workload" != "bytestream_n1_append" ]; then
      echo "very bad thing... read workload not found"
      exit 1
    fi
  fi
fi

if [ ${read_expr} != "dne" ]; then

ename="pool-${pool}_expr-${read_expr}"
ename="${ename}_sw-${stripe_width}"
ename="${ename}_es-${entry_size}"
ename="${ename}_qd-${qdepth}"
ename="${ename}_pg-${pgnum}"
ename="${ename}_rt-${read_runtime}"
ename="${ename}_if-${interface}"
ename="${ename}_ms-${maxseq}"

sudo stop ceph-osd id=0 || true
sudo stop ceph-osd id=0 || true
sudo service ceph-osd-all stop || true
sudo service ceph-osd-all stop || true
sudo sync
echo 3 | sudo tee /proc/sys/vm/drop_caches
sudo start ceph-osd id=0 || true
sudo service ceph-osd-all start || true

cat /sys/fs/cgroup/blkio/blkio.throttle.write_iops_device || true
cat /sys/fs/cgroup/blkio/blkio.throttle.read_iops_device || true

docker run --net=host \
  -v $logdir:$guest_logdir \
  -v /etc/ceph:/etc/ceph \
  -it zlog-pd \
  --pool $pool \
  --workload ${read_expr} \
  --stripe-width $stripe_width \
  --entry-size $entry_size \
  --queue-depth $qdepth \
  --runtime $read_runtime \
  --interface vanilla \
  --output $guest_logdir/$ename \
  --maxseq $maxseq

fi

set +x

done
done
done
done
done
done

}
