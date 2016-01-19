#!/bin/bash

stripe=5
num_stripes=1999
total=$(($num_stripes+1))
append_size=$((500000/$total))
./create
./append $append_size
for i in `seq 1 $num_stripes`;
do
  stripe=$((2+$stripe))
  echo $stripe
  ./zlog-change-layout new_log pool_1234 $stripe 
  ./append $append_size
done
