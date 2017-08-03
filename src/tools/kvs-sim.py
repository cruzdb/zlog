import sys
import csv
import json
from collections import defaultdict
import numpy as np
#import pandas as pd
import seaborn as sns
import matplotlib.pyplot as plt
from matplotlib import rcParams

rcParams.update({'figure.autolayout': True})


class LogDist(object):
    __slots__ = ('nobjs')

    def __init__(self, nobjs):
        self.nobjs = nobjs

    def address(self, pos):
        oid = pos % self.nobjs
        return oid

class NodePtr(object):
    __slots__ = ('nil', 'same', 'pos', 'off')

    def __init__(self, pos, ptr):
        self.nil = ptr["nil"]
        self.same = ptr["self"]
        if self.same:
            self.pos = pos
        else:
            self.pos = ptr["csn"]
        self.off = ptr["off"]

class Node(object):
    __slots__= ('key', 'val', 'red', 'left', 'right')

    def __init__(self, pos, node):
        self.key = int(node["key"])
        self.val = int(node["val"])
        self.red = node["red"]
        self.left = NodePtr(pos, node["left"])
        self.right = NodePtr(pos, node["right"])

class Log(object):
    __slots__ = ('_entries')

    def __init__(self, f, stop_after=None):
        # read the trace file and build an index
        tmp = {}
        for line in f.xreadlines():
            entry = json.loads(line)
            pos = entry["pos"]
            assert pos not in tmp
            nodes = []
            for node in entry["tree"]:
                n = Node(pos, node)
                nodes.append(n)
            tmp[pos] = (nodes, entry["bytes"])
            if stop_after is not None:
                stop_after -= 1
                if stop_after == 0:
                    break

        # rebuild for direct indexing
        maxpos = max(tmp)
        self._entries = (maxpos + 1) * [None]
        for k, v in tmp.iteritems():
            self._entries[k] = v

    def read(self, pos, dist):
        address = dist.address(pos)
        tree, nbytes = self._entries[pos]
        return tree, nbytes, address

    def snapshots(self):
        snapshots = []
        for i in range(len(self._entries)):
            if self._entries[i] is not None:
                snapshots.append(i)
        return snapshots

# this database is the most basic. ever access is counted as a
# pointer resolution
class Database(object):
    def __init__(self, log, width, snapshot=None):
        self.log = log
        self.dist = LogDist(width)
        self.snapshot = snapshot if snapshot is not None else -1

        self.last_address = None

        # stats
        self.total_resolves = 0
        self.obj_resolves = 0
        self.remote_resolves = 0
        self.nbytes = 0

    def _get_snapshot(self, update_stats=True):
        tree, nbytes, addr = self.log.read(self.snapshot, self.dist)
        if update_stats:
            self.total_resolves += 1
            self.remote_resolves += 1
            self.nbytes += nbytes
        self.last_address = addr
        return tree[-1] if tree else None

    def _resolve(self, ptr, update_stats=True):
        if ptr.nil:
            return None

        tree, nbytes, addr = self.log.read(ptr.pos, self.dist)

        if update_stats:
            self.total_resolves += 1
            assert self.last_address is not None
            if addr == self.last_address:
                # if the address of the node in which we are trying to follow is
                # the same as the last address, then in a hypothetical system in which
                # we could do a resolution in an object, then this counts that
                # scenario.
                self.obj_resolves += 1
            else:
                self.last_address = addr
                self.remote_resolves += 1
                self.nbytes += nbytes

        return tree[ptr.off]

    # return all keys. doesn't affect stats
    def keys(self):
        keys = []
        stack = []
        node = self._get_snapshot(False)
        while len(stack) > 0 or node:
            if node:
                stack.append(node)
                node = self._resolve(node.left, False)
            else:
                node = stack.pop()
                keys.append(node.key)
                node = self._resolve(node.right, False)
        return keys

    def get(self, key):
        curr = self._get_snapshot()
        while curr:
            if curr.key == key:
                return curr.val
            elif curr.key > key:
                curr = self._resolve(curr.left)
            else:
                curr = self._resolve(curr.right)
        return None

def plot(ax, x, l):
    n = np.arange(1, len(x)+1) / np.float(len(x))
    xs = np.sort(x)
    ax.step(xs, n, label=l)

figs = {}
noopt_fig = plt.subplots(figsize=(8,4))
widths = (1, 2, 4, 8, 16, 32, 64, 128, 1024)
for width in widths:
    fig, ax = plt.subplots(figsize=(8,4))
    figs[width] = fig, ax

log = Log(sys.stdin)
snapshots = log.snapshots()
for snapshot in snapshots[4500:4501]:
    keys = Database(log, 1, snapshot).keys()
    for width in widths:
        nresolves = []
        for key in keys:
            db = Database(log, width, snapshot)
            assert db.get(key) is not None
            nresolves.append(db.remote_resolves)
        for w, f in figs.iteritems():
            if w >= width:
                plot(f[1], nresolves, `width`)
    nresolves = []
    for key in keys:
        db = Database(log, 1, snapshot)
        assert db.get(key) is not None
        nresolves.append(db.total_resolves)
    for f in figs.itervalues():
        plot(f[1], nresolves, 'no-opt')

count = 0
for f in figs.itervalues():
    f[1].set_ylabel('Probability')
    f[1].set_xlabel('Pointer Hops')
    f[1].legend()
    f[0].savefig("%d.png" % (count,))
    count += 1

#    width_db = (Database(log, w, snapshot) for w in (1, 10, 100))
#    for db in width_db:
#        
#
#
#    nresolves = []
#    rresolves = []
#    for key in keys:
#        db = Database(log, dist, snapshot)
#        assert db.get(key) is not None
#        nresolves.append(db.total_resolves)
#        rresolves.append(db.remote_resolves)
#    print len(nresolves)
#    tmp = pd.DataFrame({'resolves': nresolves, 'remote': rresolves})
#    df = df.append(tmp)
#
#
#def plot(ax, x):
#    x = x.values
#    n = np.arange(1, len(x)+1) / np.float(len(x))
#    xs = np.sort(x)
#    ax.step(xs, n)
#
#plot(ax, df['resolves'])
#plot(ax, df['remote'])

#ax.hist(df['resolves'], normed=1,
#        histtype='step', bins=50, cumulative=True)
#ax.hist(df['remote'], bins=50, normed=1,
#        histtype='step', cumulative=True)
#fig.savefig('x.png')

#p = sns.distplot(df, hist=False, kde_kws=dict(cumulative=True))
#p = sns.distplot(df, hist_kws=dict(cumulative=True), kde=False)
#p = sns.distplot(df['remote'], hist=False, kde_kws=dict(cumulative=True))
#p.get_figure().savefig('x.png')

#df = pd.DataFrame({'resolves': [], 'freq': []})
#nresolves = defaultdict(lambda: 0)
#nresolves[db.total_resolves] += 1
#tmp = pd.DataFrame({'resolves': nresolves.keys(),
#                    'freq': nresolves.values()})
#df = df.append(tmp)
#p = sns.boxplot(x='resolves', y='freq', data=df)
#p.get_figure().savefig('x.png')

#writer = csv.writer(sys.stdout)
#writer.writerow(("snapshot", "total_resolves", "nbytes"))
#
#snapshots = log.snapshots()
#for snapshot in snapshots:
#    db = Database(log, snapshot)
#    assert db.get(-1) is None
#    db.keys()
#    writer.writerow((snapshot, db.total_resolves, db.nbytes))
