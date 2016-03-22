import sys
import glob
import os
import pandas as pd
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter
import numpy as np

matplotlib.style.use('ggplot')

def plot_throughput(traces):
    tps = []
    for fn, trace in traces:
        trace = trace.set_index('completed')
        trace = trace.resample('S', how='count')
        trace = pd.rolling_mean(trace.latency, window=30, min_periods=1)
        trace = trace.reset_index('completed')
        tps.append((fn, trace))

    if len(tps) == 1:
        agg_fn = tps[0][0]
    else:
        agg_fn = "multi_" + `len(tps)` + ".log"
    
    plt.figure()
    for fn, trace in tps:
        plt.plot(trace.completed, trace.latency, label=fn)
    plt.gca().xaxis.set_major_formatter(ScalarFormatter())
    plt.title('I/O Throughput')
    plt.ylabel('IOs per Second')
    plt.xlabel('Time')
    lgd = plt.legend(loc='center left', bbox_to_anchor=(1, 0.5))
    plt.savefig(agg_fn + '_iops.png', format='png',
            bbox_extra_artists=(lgd,), bbox_inches='tight')

def plot_latency_ecdf(traces):
    cdfs = []
    for fn, trace in traces:
        sorted_latency = np.sort(trace.latency)
        yvals = np.arange(len(sorted_latency)) / float(len(sorted_latency))
        cdfs.append((fn, sorted_latency, yvals))

    if len(cdfs) == 1:
        agg_fn = cdfs[0][0]
    else:
        agg_fn = "multi_" + `len(cdfs)` + ".log"
    
    plt.figure()
    for fn, sorted_latency, yvals in cdfs:
        plt.plot(sorted_latency, yvals, label=fn)
    plt.gca().xaxis.set_major_formatter(ScalarFormatter())
    plt.title('I/O Latency CDF')
    plt.xlabel('Latency (ms)')
    plt.ylabel('Frequency')
    lgd = plt.legend(loc='center left', bbox_to_anchor=(1, 0.5))
    plt.savefig(agg_fn + '_ecdf.png', format='png',
            bbox_extra_artists=(lgd,), bbox_inches='tight')
    
    plt.figure()
    for fn, sorted_latency, yvals in cdfs:
        plt.plot(sorted_latency, yvals, label=fn)
    plt.xscale('log')
    plt.gca().xaxis.set_major_formatter(ScalarFormatter())
    plt.title('I/O Latency CDF')
    plt.xlabel('Latency (ms)')
    plt.ylabel('Frequency')
    lgd = plt.legend(loc='center left', bbox_to_anchor=(1, 0.5))
    plt.savefig(agg_fn + '_ecdf_logx.png', format='png',
            bbox_extra_artists=(lgd,), bbox_inches='tight')

def plot_combos(traces):
    for trace in traces:
        plot_latency_ecdf([trace])
        plot_throughput([trace])
    plot_latency_ecdf(traces)
    plot_throughput(traces)

def read_trace(filename):
    trace = pd.read_table(filename, sep=" ", header=None,
            names=("completed", "latency"))
    trace.completed = pd.to_datetime(trace.completed, unit="ns")
    trace.completed = trace.completed - min(trace.completed)
    trace.latency = pd.to_timedelta(trace.latency, unit="ns")
    trace.latency = trace.latency / pd.Timedelta(milliseconds=1)
    trace.sort_values(by='completed', ascending=True, inplace=True)
    return trace

def read_traces(filenames):
    return [(os.path.basename(fn), read_trace(fn)) for fn in filenames]

if __name__ == '__main__':
    traces = []
    for arg in sys.argv[1:]:
        traces += glob.glob(arg)
    traces = read_traces(traces)
    plot_combos(traces)
