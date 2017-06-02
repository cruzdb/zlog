set key autotitle columnhead
set datafile separator ","
set xlabel 'snapshot'
set ylabel 'resolve count'
set y2label 'bytes read'
set ytics nomirror
set y2tics
set autoscale y
set autoscale y2
plot 'sim.dat' using 1:2 axes x1y1, '' using 1:3 axes x1y2
