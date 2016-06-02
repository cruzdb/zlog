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
    
    fig = plt.figure()
    ax = fig.add_subplot(111)
    for fn, trace in tps:
        ax.plot(trace.completed, trace.latency, label=fn)
    ax.xaxis.set_major_formatter(ScalarFormatter())
    ax.set_title('I/O Throughput: ' + agg_fn)
    ax.set_ylabel('IOs per Second')
    ax.set_xlabel('Time')
    fig.savefig(agg_fn + '_iops.png', format='png')
    #lgd = ax.legend(loc='center left', bbox_to_anchor=(1, 0.5))
    #fig.savefig(agg_fn + '_iops.png', format='png',
    #        bbox_extra_artists=(lgd,), bbox_inches='tight')
    plt.close(fig)

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
    
    fig = plt.figure()
    ax = fig.add_subplot(111)
    for fn, sorted_latency, yvals in cdfs:
        ax.plot(sorted_latency, yvals, label=fn)
    ax.set_xscale('log')
    ax.xaxis.set_major_formatter(ScalarFormatter())
    ax.set_title('I/O Latency CDF: ' + agg_fn)
    ax.set_xlabel('Latency (ms)')
    ax.set_ylabel('Frequency')
    fig.savefig(agg_fn + '_ecdf_logx.png', format='png')
    #lgd = ax.legend(loc='center left', bbox_to_anchor=(1, 0.5))
    #fig.savefig(agg_fn + '_ecdf_logx.png', format='png',
    #        bbox_extra_artists=(lgd,), bbox_inches='tight')
    plt.close(fig)
    return

    fig = plt.figure()
    ax = fig.add_subplot(111)
    for fn, sorted_latency, yvals in cdfs:
        ax.plot(sorted_latency, yvals, label=fn)
    ax.xaxis.set_major_formatter(ScalarFormatter())
    ax.set_title('I/O Latency CDF')
    ax.set_xlabel('Latency (ms)')
    ax.set_ylabel('Frequency')
    lgd = ax.legend(loc='center left', bbox_to_anchor=(1, 0.5))
    fig.savefig(agg_fn + '_ecdf.png', format='png',
            bbox_extra_artists=(lgd,), bbox_inches='tight')
    plt.close(fig)

def read_trace(filename):
    trace = pd.read_table(filename, sep=" ", header=None,
            names=("completed", "latency"))
    trace.completed = pd.to_datetime(trace.completed, unit="ns")
    trace.completed = trace.completed - min(trace.completed)
    trace.latency = pd.to_timedelta(trace.latency, unit="ns")
    trace.latency = trace.latency / pd.Timedelta(milliseconds=1)
    trace.sort_values(by='completed', ascending=True, inplace=True)
    return trace

def plot_traces(traces):
    for fn in traces:
        df = read_trace(fn)
        name = os.path.basename(fn)
        plot_latency_ecdf([(name, df)])
        plot_throughput([(name, df)])

if __name__ == '__main__':
    traces = []
    for arg in sys.argv[1:]:
        traces += glob.glob(arg)
    plot_traces(traces)
