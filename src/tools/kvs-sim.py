import sys
import csv
import json

class NodePtr(object):
    __slots__ = ('nil', 'same', 'pos', 'off')
    def __init__(self, logpos, ptr):
        self.nil = ptr["nil"]
        self.same = ptr["self"]
        if self.same:
            self.pos = logpos
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
    __slots__ = ('entries')
    def __init__(self, f):
        # build index of log entries
        tmp = {}
        for line in sys.stdin.xreadlines():
            entry = json.loads(line)
            pos = entry["pos"]
            assert pos not in tmp
            nodes = []
            for node in entry["tree"]:
                n = Node(pos, node)
                nodes.append(n)
            tmp[pos] = (nodes, entry["bytes"])
        # move to list for direct indexing
        maxpos = max(tmp)
        self.entries = (maxpos + 1) * [None]
        for k, v in tmp.iteritems():
            self.entries[k] = v

    def written_positions(self):
        snapshots = []
        for i in range(len(self.entries)):
            if self.entries[i] is not None:
                snapshots.append(i)
        return snapshots

class Database(object):
    def __init__(self, log, snapshot=None):
        self.log = log
        if snapshot is None:
            snapshot = -1
        tree, nbytes = self.log.entries[snapshot]
        self.root = tree[-1] if tree else None

        # stats
        self.resolves = 1
        self.nbytes = nbytes

    def resolve(self, ptr):
        if ptr.nil:
            return None
        self.resolves += 1
        tree, nbytes = self.log.entries[ptr.pos]
        self.nbytes += nbytes
        return tree[ptr.off]

    def get(self, key):
        curr = self.root
        while curr:
            if curr.key == key:
                return curr.val
            elif curr.key > key:
                curr = self.resolve(curr.left)
            else:
                curr = self.resolve(curr.right)
        return None

log = Log(sys.stdin)

writer = csv.writer(sys.stdout)
writer.writerow(("snapshot", "resolves", "nbytes"))
snapshots = log.written_positions()
for snapshot in snapshots:
    db = Database(log, snapshot)
    assert db.get(-1) is None
    writer.writerow((snapshot, db.resolves, db.nbytes))
