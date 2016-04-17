#!/bin/bash

set -e

while [[ $# > 1 ]]; do
  key="$1"
  case $key in
    -p|--pool)
      pool="$2"
      shift # past argument
      ;;
    -g|--pgnum)
      pgnum="$2"
      shift # past argument
      ;;
    -w|--workload)
      workload="$2"
      shift
      ;;
    -s|--stripe-width)
      stripe_width="$2"
      shift
      ;;
    -e|--entry-size)
      entry_size="$2"
      shift
      ;;
    -q|--queue-depth)
      qdepth="$2"
      shift
      ;;
    -r|--runtime)
      runtime="$2"
      shift
      ;;
    -i|--interface)
      interface="$2"
      shift
      ;;
    -d|--dir)
      outdir="$2"
      shift
      ;;
    -o|--output)
      output="$2"
      shift
      ;;
    --deps)
      deps=$2
      shift
      ;;
    --rest)
      rest=$2
      shift
      ;;
    *)
      # unknown option
      ;;
  esac
  shift # past argument or value
done 

# just want to copy out the ceph dependencies
if [ ! -z "$deps" ]; then
 cp /usr/lib/rados-classes/libcls_zlog_bench.so $deps
 exit 0
fi

set -x

# start with a fresh pool for the experiment
ceph osd pool delete $pool $pool --yes-i-really-really-mean-it || true
ceph osd pool create $pool $pgnum $pgnum replicated
ceph osd pool set $pool size 1

# wait for ceph health ok and finished creating
while true; do
  if ceph status | tee /dev/tty | grep -q HEALTH_OK; then
    if ! ceph status | tee /dev/tty | grep -q creating; then
      break
    fi
  fi
  sleep 1
done

set +x

if [ ! -z "$rest" ]; then
  echo "Letting Ceph rest for a while ($rest secs) ..."
  sleep $rest
fi

# run experiment
pushd /src/zlog/src

# build output log filename
ceph_ver=$(ceph --version | awk '{print $3}')
ceph_sha=$(ceph --version | awk '{print $4}' | cut -d "(" -f 2 | cut -c1-8)
output="${output}_cv-${ceph_ver}"
output="${output}_cs-${ceph_sha}"
output="${output}.tp.log"
output_path=$outdir/$output

# build args to experiment runner
args="--pool $pool"
args="$args --experiment $workload"
args="$args --stripe_width $stripe_width"
args="$args --entry_size $entry_size"
args="$args --qdepth $qdepth"
args="$args --tp 5"
args="$args --perf_file $output_path"
args="$args --runtime $runtime"
args="$args --interface $interface"

set -x

echo "Running: ./physical-design $args"
./physical-design $args

set +x
