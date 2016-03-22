num_pg=10
pool=rbd
# derive from tuning
qdepth=10
waitsec=10
# we only do fixed size right now
entry_size=4096

# names of the experiments to be run
experiments_11="map_11 bytestream_11"
experiments_n1="map_n1 bytestream_n1_write bytestream_n1_append"

# 1:1 workloads use stripe width = 0
for exp in $experiments_11; do
  bench/run-physical-design.sh $pool $exp 0 $entry_size $qdepth $waitsec
done

# n:1 workloads use stripe width
num_pg2x=$(($num_pg * 2))
for exp in $experiments_n1; do
  for sw in "1" "$num_pg" "$num_pg2x"; do
    bench/run-physical-design.sh $pool $exp $sw $entry_size $qdepth $waitsec
  done
done
