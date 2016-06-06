#!/bin/bash
set -e
set -x

SEQ="mon0"
CLIENTS="osd0 client0"
POOL=rbd
LOGNAME=
PORT=5678
RUNTIME=600
QDEPTH=5
ENTRY_SIZE=

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

# start the clients
#   - this won't work with multiple clients running per node. to fix for this
#   case avoid --name and stash the container id in an array for each host
for host in $CLIENTS; do
  ssh $host sudo docker kill zlog || true
  ssh $host sudo docker rm zlog || true
  ssh $host sudo docker run -d --name zlog -v /etc/ceph:/etc/ceph --net=host \
    -it zlog/zlog:jewel zlog-bench --pool $POOL --server $SEQ --port $PORT \
    --runtime $RUNTIME --qdepth $QDEPTH --iops-log /iops.log
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
  ssh $host sudo docker cp zlog:/iops.log - | tar -xOf - iops.log > ${host}.iops.log
  ssh $host sudo docker rm zlog || true
done
