import sys
import numpy as np
import matplotlib.pyplot as plt
from matplotlib import rcParams
rcParams.update({'figure.autolayout': True})
from matplotlib.ticker import MaxNLocator
import seaborn as sns
import kvs

sns.set_style("whitegrid", {'grid.linestyle': '--'})

def plot_cdf(ax, x, l):
    n = np.arange(1, len(x)+1) / np.float(len(x))
    xs = np.sort(x)
    ax.step(xs, n, label=l)

# plot the length of each path in the db
def add_path_lengths(db, ax, name):
    lens = map(lambda p: len(p), db.paths())
    plot_cdf(ax, lens, name)

# plot the frequency of each path address
def add_path_unique(db, ax, name):
    freqs = map(lambda path:
            len(set(map(lambda (n,a): a, path))),
            db.paths())
    plot_cdf(ax, freqs, name)

def add_path_adjacent(db, ax, name):
    def collapse(path):
        count = 0
        curr = None
        for path, addr in path:
            assert addr != None
            if addr == curr:
                continue
            curr = addr
            count += 1
        return count
    lens = map(lambda p: collapse(p), db.paths())
    plot_cdf(ax, lens, name)

# prepare an empty figure for each of the striping
# widths that will be simulated
figs = {}
widths = (1, 2, 4, 8, 16, 32, 64, 128, 1024)
for width in widths:
    fig, ax = plt.subplots(figsize=(8,4))
    figs[width] = fig, ax

log = kvs.Log(sys.stdin)
snapshot = log.latest_snapshot()

for width in widths:
    fig, ax = figs[width]
    db = kvs.Database(log, width, snapshot)
    add_path_unique(db, ax, "uniq-" + `width`)
    add_path_adjacent(db, ax, "simp-" + `width`)
    add_path_lengths(db, ax, "naive")

count = 0
for fig, ax in figs.itervalues():
    ax.set_ylabel('Probability')
    ax.set_xlabel('Unique Partitions')
    ax.legend()
    ax.set_ylim(bottom=0.0, top=1.0)
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    fig.savefig("%d.png" % (count,))
    count += 1
