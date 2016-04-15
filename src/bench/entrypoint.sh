#!/bin/bash

set -x
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
    -o|--output)
      output="$2"
      shift
      ;;
    *)
      # unknown option
      ;;
  esac
  shift # past argument or value
done 

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

# run experiment
pushd /src/zlog/src

args="--pool $pool"
args="$args --experiment $workload"
args="$args --stripe_width $stripe_width"
args="$args --entry_size $entry_size"
args="$args --qdepth $qdepth"
args="$args --tp 5"
args="$args --perf_file $output"
args="$args --runtime $runtime"
args="$args --interface $interface"

echo "Running: ./physical-design $args"
./physical-design $args
