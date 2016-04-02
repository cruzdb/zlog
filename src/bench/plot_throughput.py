import sys
import glob
import os
import pandas as pd
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter
import numpy as np

matplotlib.style.use('ggplot')

def plot_throughput(name, df, ax=None):
    df.throughput = pd.rolling_mean(df.throughput, window=5, min_periods=1)
    ax.plot(df.completed, df.throughput, label=name)
    ax.set_title('Single OSD Append Throughput (Jewel 2016)')
    ax.set_ylabel('Appends per Second per OSD')
    ax.set_xlabel('Time')

def read_trace(filename):
    trace = pd.read_table(filename, sep=" ", header=None,
            names=("completed", "throughput"))
    # shift timeseries to have zero start time
    trace.completed = pd.to_datetime(trace.completed, unit="ns")
    trace.completed = trace.completed - min(trace.completed)
    trace.sort_values(by='completed', ascending=True, inplace=True)
    return trace

def plot_traces(traces, combine):
    if combine:
        fig = plt.figure()
        ax = fig.add_subplot(111)

    for fn in traces:
        df = read_trace(fn)
        name = os.path.basename(fn)

        if not combine:
            fig = plt.figure()
            ax = fig.add_subplot(111)

        plot_throughput(name, df, ax)

        if not combine:
            fig.savefig(name + '_iops.png', format='png')
            plt.close(fig)

    if combine:
        fig.savefig('combined_iops.png', format='png')
        plt.close(fig)

if __name__ == '__main__':
    traces = []
    for arg in sys.argv[1:]:
        traces += glob.glob(arg)
    plot_traces(traces, True)
