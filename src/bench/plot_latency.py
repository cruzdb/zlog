import sys
import pandas as pd
import matplotlib
import matplotlib.pyplot as plt
import numpy as np

matplotlib.style.use('ggplot')

with open(sys.argv[1]) as f:
    table = pd.read_table(f, sep=" ", header=None,
        names=("start", "latency"))

# use zero start time in seconds
table['start'] = table['start'] - min(table['start'])
table['start'] = table['start'] / (10.0**9)
# convert from ns to ms
table['latency'] = table['latency'] / (10.0**6)

def time_series():
    ax = table.plot(x='start', y='latency')
    ax.set_xlabel("time (sec)")
    ax.set_ylabel("latency (ms)")
    ax.set_title("I/O Latency")

def ecdf():
    sl = np.sort(table["latency"])
    yvals = np.arange(len(sl)) / float(len(sl))
    plt.figure()
    plt.plot(sl, yvals)
    plt.title("I/O Latency CDF")
    plt.xlabel("Latency (ms)")
    plt.ylabel("Frequency")

def heatmap():
    # TODO: http://www.brendangregg.com/HeatMaps/latency.html
    return

def kern_density():
    # the freq seems to be above 1.0...
    return
    plt.figure()
    table["latency"].plot(kind='kde')

def throughput():
    # sliding window throughput counting
    # group by start (per-sec) then rolling avg
    return

kern_density()
heatmap()
time_series()
ecdf()
throughput()

plt.show()
