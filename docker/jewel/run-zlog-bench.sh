#!/bin/bash
set -e

this_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

PORT=5678
OUTDIR=$PWD

while [[ $# > 1 ]]; do
  key="$1"
  case $key in
    -s|--seq)
      SEQ="$2"
      shift # past argument
      ;;
    -c|--client)
      if [ -z "$CLIENTS" ]; then CLIENTS="$2";
      else CLIENTS="$CLIENTS $2"; fi
      shift
      ;;
    --pool)
      POOL="$2"
      shift
      ;;
    --port)
      PORT="$2"
      shift
      ;;
    -r|--runtime)
      RUNTIME="$2"
      shift
      ;;
    -q|--qdepth)
      QDEPTH="$2"
      shift
      ;;
    -l|--logname)
      LOGNAME="$2"
      shift
      ;;
    -e|--entry-size)
      ENTRY_SIZE="$2"
      shift
      ;;
    -o|--outdir)
      OUTDIR="$2"
      shift
      ;;
    *)
      echo "Unknown option $2"
      exit 1
      ;;
  esac
  shift # past argument or value
done 

echo "########### SETTINGS ##########"
echo "       SEQ: $SEQ"
echo "      PORT: $PORT"
echo "   CLIENTS: $CLIENTS"
echo "      POOL: $POOL"
echo "  LOG NAME: $LOGNAME"
echo "ENTRY SIZE: $ENTRY_SIZE"
echo "   Q DEPTH: $QDEPTH"
echo "   RUNTIME: $RUNTIME"
echo "    OUTDIR: $OUTDIR"
echo "###############################"

# install docker and zlog image
function install_docker() {
  install_docker_script=`base64 -w0 ${this_dir}/install-docker.sh`
  for host in $SEQ $CLIENTS; do
    ssh $host "echo $install_docker_script | base64 -d | sudo bash"
  
    # perhaps make the pull optional to reduce amount of chances we have network
    # issues
    ssh $host sudo docker pull zlog/zlog:jewel
  done
}

# ntp refresh
function time_sync() {
  for host in $SEQ $CLIENTS; do
    ssh $host sudo service ntp stop
    ssh $host sudo ntpd -gq
    ssh $host sudo service ntp start
  done
}

# start the sequencer
function start_seq() {
  ssh $SEQ sudo docker kill seqr || true
  ssh $SEQ sudo docker rm seqr || true
  ssh $SEQ sudo docker run -d --name=seqr -v /etc/ceph:/etc/ceph \
    --net=host -it zlog/zlog:jewel zlog-seqr --port $PORT --report-sec 2
}

# sequencer benchmark
function bench_seq() {
  for host in $CLIENTS; do 
    ssh $host sudo docker kill zlog || true
    ssh $host sudo docker rm zlog || true
    ssh $host sudo docker run -d --name zlog -v /etc/ceph:/etc/ceph --net=host \
      -it zlog/zlog:jewel zlog-bench --nextseq --pool $POOL --server $SEQ --port $PORT \
      --runtime $2 --logname ${LOGNAME}_seqtest --iops-log /$1
  done
}

# post log tail from each container
function test_wait() {
  start=`date +%s`
  while [ 1 ]; do
    echo "Posting logs from sequencer on host $SEQ"
    ssh $SEQ sudo docker logs --tail=10 seqr
    for host in $CLIENTS; do
      echo "Posting logs from client on host $host"
      ssh $host sudo docker logs --tail=10 zlog
    done
    sleep 10
  
    now=`date +%s`
    tgt=$(( $start + $1 ))
    if [ $now -gt $tgt ]; then
      break
    fi
  done
}

# collect data and clean-up containers
function collect() {
  for host in $CLIENTS; do
    fn="${2}_h-${host}.log"
    ssh $host sudo docker kill zlog || true
    ssh $host sudo docker cp zlog:/$1 - | tar -xOf - $1 > ${OUTDIR}/$fn
    ssh $host sudo docker rm zlog || true
  done
}

# start the append clients
#   - this won't work with multiple clients running per node. to fix for this
#   case avoid --name and stash the container id in an array for each host
function append() {
  for host in $CLIENTS; do
    ssh $host sudo docker kill zlog || true
    ssh $host sudo docker rm zlog || true
    ssh $host sudo docker run -d --name zlog -v /etc/ceph:/etc/ceph --net=host \
      -it zlog/zlog:jewel zlog-bench --append --pool $POOL --server $SEQ --port $PORT \
      --runtime $RUNTIME --qdepth $QDEPTH --entry-size $ENTRY_SIZE --logname $LOGNAME \
      --iops-log /$1
  done
}

function stop_seq() {
  ssh $SEQ sudo docker kill seqr || true
  ssh $SEQ sudo docker rm seqr || true
}

# setup
install_docker
#time_sync

start_seq

# short sequencer benchmark
bench_seq seq-iops.log 60
test_wait 60
collect seq-iops.log "seqtest_rt-60"

# run append test
append append-iops.log
test_wait $RUNTIME
collect append-iops.log "append_rt-${RUNTIME}_p-${POOL}_qd-${QDEPTH}_ln-${LOGNAME}_es-${ENTRY_SIZE}"

stop_seq
