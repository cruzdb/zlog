#!/bin/bash
set -e

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
echo "###############################"

# install docker and zlog image
install_docker_script=`base64 -w0 install-docker.sh`
for host in $SEQ $CLIENTS; do
  ssh $host "echo $install_docker_script | base64 -d | sudo bash"

  # perhaps make the pull optional to reduce amount of chances we have network
  # issues
  ssh $host sudo docker pull zlog/zlog:jewel
done

# ntp refresh
for host in $SEQ $CLIENTS; do
  ssh $host sudo service ntp stop
  ssh $host sudo ntpd -gq
  ssh $host sudo service ntp start
done

# start the sequencer
ssh $SEQ sudo docker kill seqr || true
ssh $SEQ sudo docker rm seqr || true
ssh $SEQ sudo docker run -d --name=seqr -v /etc/ceph:/etc/ceph \
  --net=host -it zlog/zlog:jewel zlog-seqr --port $PORT --report-sec 2

# test the sequencer throughput
for host in $CLIENTS; do 
  ssh $host sudo docker kill zlog || true
  ssh $host sudo docker rm zlog || true
  ssh $host sudo docker run -d --name zlog -v /etc/ceph:/etc/ceph --net=host \
    -it zlog/zlog:jewel zlog-bench --nextseq --pool $POOL --server $SEQ --port $PORT \
    --runtime 60 --logname ${LOGNAME}_seqtest --iops-log /seq-iops.log
done

# post log tail from each container
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
  tgt=$(( $start + 60 ))
  if [ $now -gt $tgt ]; then
    break
  fi
done

# note that between the sequencer throughput test and the append test we alter
# the log name. the reason we do this is because the sequencer test will
# result in a log with a very large value for the tail such that when the
# append test begins the clients will start appending to a very very long but
# empty log. this may or may not be desirable.
#
# an alternative is to just restart the sequencer

# collect data and clean-up containers
for host in $CLIENTS; do
  ssh $host sudo docker kill zlog || true
  ssh $host sudo docker cp zlog:/seq-iops.log - | tar -xOf - seq-iops.log > ${host}.seq.iops.log
  ssh $host sudo docker rm zlog || true
done

# start the append clients
#   - this won't work with multiple clients running per node. to fix for this
#   case avoid --name and stash the container id in an array for each host
for host in $CLIENTS; do
  ssh $host sudo docker kill zlog || true
  ssh $host sudo docker rm zlog || true
  ssh $host sudo docker run -d --name zlog -v /etc/ceph:/etc/ceph --net=host \
    -it zlog/zlog:jewel zlog-bench --append --pool $POOL --server $SEQ --port $PORT \
    --runtime $RUNTIME --qdepth $QDEPTH --entry-size $ENTRY_SIZE --logname $LOGNAME \
    --iops-log /append-iops.log
done

# post log tail from each container
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
  tgt=$(( $start + $RUNTIME ))
  if [ $now -gt $tgt ]; then
    break
  fi
done

# collect data and clean-up containers
ssh $SEQ sudo docker kill seqr || true
ssh $SEQ sudo docker rm seqr || true
for host in $CLIENTS; do
  ssh $host sudo docker kill zlog || true
  ssh $host sudo docker cp zlog:/append-iops.log - | tar -xOf - append-iops.log > ${host}.append.iops.log
  ssh $host sudo docker rm zlog || true
done
