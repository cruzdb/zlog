#!/bin/bash
set -e

this_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

PORT=5678
OUTDIR=$PWD
CLIENT_INSTANCES=1
STORE_VER=1
STRIPE_WIDTH="-1"
CLIENT_NODES=()

while [[ $# > 1 ]]; do
  key="$1"
  case $key in
    -s|--seq)
      SEQ="$2"
      shift # past argument
      ;;
    -c|--client)
      CLIENT_NODES+=($2)
      shift
      ;;
    --client-instances)
      CLIENT_INSTANCES="$2"
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
    --context)
      CONTEXT="$2"
      shift
      ;;
    --store-ver)
      STORE_VER="$2"
      shift
      ;;
    --stripe-width)
      STRIPE_WIDTH="$2"
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
echo "         SEQ: $SEQ"
echo "        PORT: $PORT"
echo "CLIENT NODES: ${CLIENT_NODES[@]}"
echo "        POOL: $POOL"
echo "    LOG NAME: $LOGNAME"
echo "  ENTRY SIZE: $ENTRY_SIZE"
echo "     Q DEPTH: $QDEPTH"
echo "     RUNTIME: $RUNTIME"
echo "      OUTDIR: $OUTDIR"
echo "CLIENT INSTS: $CLIENT_INSTANCES"
echo "STORE VERSIN: $STORE_VER"
echo "STRIPE WIDTH: $STRIPE_WIDTH"
echo "###############################"

if [ $CLIENT_INSTANCES -gt 10 ]; then
  echo "Client instances too large. Max 10"
  exit 1
fi

# create container names for this experiment
i=0
client_cont_names=()
while [ $i -lt $CLIENT_INSTANCES ]; do
  client_cont_names+=("zlog_bench_$i")
  i=$(($i+1))
done

# create all possible cont names to make
# cleanup easier
i=0
all_client_cont_names=()
while [ $i -lt 10 ]; do
  all_client_cont_names+=("zlog_bench_$i")
  i=$(($i+1))
done

# install docker and zlog image
function install_docker() {
  install_docker_script=`base64 -w0 ${this_dir}/install-docker.sh`
  for host in $SEQ ${CLIENT_NODES[@]}; do
    ssh $host "echo $install_docker_script | base64 -d | sudo bash"
  
    # perhaps make the pull optional to reduce amount of chances we have network
    # issues
    ssh $host sudo docker pull zlog/zlog:jewel
  done
}

# ntp refresh
#function time_sync() {
#  for host in $SEQ $CLIENTS; do
#    ssh $host sudo service ntp stop
#    ssh $host sudo ntpd -gq
#    ssh $host sudo service ntp start
#  done
#}

# start the sequencer
function start_seq() {
  ssh $SEQ sudo docker kill seqr || true
  ssh $SEQ sudo docker rm seqr || true
  ssh $SEQ sudo docker run -d --name=seqr -v /etc/ceph:/etc/ceph \
    --net=host -it zlog/zlog:jewel zlog-seqr --port $PORT \
    --report-sec 5 --iops-logfile /$1
}

# sequencer benchmark
#function bench_seq() {
#  ssh $CLIENT sudo docker kill ${all_client_cont_names[@]} || true
#  ssh $CLIENT sudo docker rm ${all_client_cont_names[@]} || true
#  for cont_name in ${client_cont_names[@]}; do
#    ssh $CLIENT sudo docker run -d --name ${cont_name} -v /etc/ceph:/etc/ceph --net=host \
#      -it zlog/zlog:jewel zlog-bench --nextseq --pool $POOL --server $SEQ --port $PORT \
#      --runtime $2 --logname ${LOGNAME}_seqtest --iops-log /$1
#  done
#}

# post log tail from each container
function test_wait() {
  start=`date +%s`
  while [ 1 ]; do
    echo "Posting logs from sequencer on host $SEQ"
    ssh $SEQ sudo docker logs --tail=10 seqr

    for host in ${CLIENT_NODES[@]}; do
      for cont_name in ${client_cont_names[@]}; do
        echo "Posting logs from client instance ${cont_name} on host $host"
        ssh $host sudo docker logs --tail=5 ${cont_name}
      done
    done

    sleep 30
  
    now=`date +%s`
    tgt=$(( $start + $1 ))
    if [ $now -gt $tgt ]; then
      break
    fi
  done
}

# collect data and clean-up containers
function collect() {
  for host in ${CLIENT_NODES[@]}; do
    ssh $host sudo docker kill ${all_client_cont_names[@]} || true
  done

  for host in ${CLIENT_NODES[@]}; do
    for cont_name in ${client_cont_names[@]}; do
      fn="${2}_h-${host}_ci-${cont_name}"
      ssh $host sudo docker cp ${cont_name}:/$1 - | tar -xOf - $1 > ${OUTDIR}/${fn}.log
      ssh $host sudo docker logs ${cont_name} > ${OUTDIR}/${fn}.cont.log
    done
  done

  for host in ${CLIENT_NODES[@]}; do
    ssh $host sudo docker rm ${all_client_cont_names[@]} || true
  done
}

# run some clients
function append() {
  # shutdown any existing containers
  for host in ${CLIENT_NODES[@]}; do
    ssh $host sudo docker kill ${all_client_cont_names[@]} || true
    ssh $host sudo docker rm ${all_client_cont_names[@]} || true
  done

  # start benchmark instances on each client node
  for host in ${CLIENT_NODES[@]}; do
    for cont_name in ${client_cont_names[@]}; do
      ssh $host sudo docker run -d --name ${cont_name} -v /etc/ceph:/etc/ceph --net=host \
        -it zlog/zlog:jewel zlog-bench --append --pool $POOL --server $SEQ --port $PORT \
        --runtime $RUNTIME --qdepth $QDEPTH --entry-size $ENTRY_SIZE --logname $LOGNAME \
        --store-ver $STORE_VER --stripe-width $STRIPE_WIDTH --iops-log /$1
    done
  done
}

function stop_collect_seq() {
  ssh $SEQ sudo docker kill seqr || true
  fn="${2}_h-${SEQ}.log"
  ssh $SEQ sudo docker cp seqr:/$1 - | tar -xOf - $1 > ${OUTDIR}/$fn
  ssh $SEQ sudo docker rm seqr || true
}

# setup
install_docker
#time_sync

prefix=""
if [ -n "$CONTEXT" ]; then
  prefix="${CONTEXT}_"
fi
prefix="${prefix}rt-${RUNTIME}_p-${POOL}_qd-${QDEPTH}_ln-${LOGNAME}_es-${ENTRY_SIZE}_iv-${STORE_VER}_sw-${STRIPE_WIDTH}"

start_seq seq-iops.log

# NOTICE: if you re-enable the sequencer benchmark here then consider that we
# save the performance logs of the seqeuencer during the real benchmark but
# don't actually restart the sequencer ensuring that the log will only
# represent the throughput of the benchmark...
#
# short sequencer benchmark
#bench_seq seq-iops.log 60
#test_wait 60
#collect seq-iops.log "seqtest_rt-60"

# run append test
append append-iops.log
test_wait $RUNTIME
collect append-iops.log "append_${prefix}"

stop_collect_seq seq-iops.log "seqr_${prefix}"
