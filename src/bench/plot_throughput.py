import sys
import glob
import os
import re
import pandas as pd
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter
import numpy as np

matplotlib.style.use('ggplot')

fn_re = re.compile("pool-(?P<pool>.+)_expr-(?P<expr>.+)_sw-(?P<sw>\d+)_es-(?P<es>\d+)_qd-(?P<qd>\d+)_rt-(?P<rt>\d+)_if-(?P<if>.+)\.log")

def plot_throughput(name, m, df, ax=None):
    df.throughput = pd.rolling_mean(df.throughput, window=5, min_periods=1)
    label = m.group('expr') + "/" + m.group('if')
    ax.plot(df.completed, df.throughput, label=label)
    ax.set_title('Single OSD Append Throughput (Jewel 2016)')
    ax.set_ylabel('Appends per Second per OSD')
    ax.set_xlabel('Time')
    ax.text(df.completed.tail(1), df.throughput.tail(1), 'asdf')

def parse_filename(filename):
    m = fn_re.match(os.path.basename(filename))
    assert m
    #print m.group('pool'), m.group('expr'), m.group('sw'), \
    #        m.group('es'), m.group('qd'), m.group('rt'), m.group('if')
    return m

def read_trace(filename, trimSecs=0):
    trace = pd.read_table(filename, sep=" ", header=None,
            names=("completed", "throughput"))
    # shift timeseries to have zero start time
    trace.completed = pd.to_datetime(trace.completed, unit="ns")
    trace.completed = trace.completed - min(trace.completed)
    trace.completed = trace.completed / pd.Timedelta(seconds=1)
    trace.sort_values(by='completed', ascending=True, inplace=True)
    return trace

def plot_traces(traces, combine):
    if combine:
        fig = plt.figure()
        ax = fig.add_subplot(111)

    for fn in traces:
        df = read_trace(fn)
        name = os.path.basename(fn)
        m = parse_filename(fn)

        if not combine:
            fig = plt.figure()
            ax = fig.add_subplot(111)

        plot_throughput(name, m, df, ax)

        if not combine:
            fig.savefig(name + '_iops.png', format='png')
            plt.close(fig)

    if combine:
        lgd = ax.legend(loc='center left', bbox_to_anchor=(1, 0.5))
        fig.savefig('combined_iops.png', format='png',
            bbox_extra_artists=(lgd,), bbox_inches='tight')
        #fig.savefig('combined_iops.png', format='png')
        plt.close(fig)

if __name__ == '__main__':
    traces = []
    for arg in sys.argv[1:]:
        traces += glob.glob(arg)
    plot_traces(traces, True)
