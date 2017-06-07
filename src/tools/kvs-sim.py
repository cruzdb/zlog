import sys
import csv
import json

class LogDist(object):
    def __init__(self, nobjs):
        self.nobjs = nobjs

    def address(self, pos):
        oid = pos % self.nobjs
        return oid

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
    __slots__ = ('dist', '_entries')
    def __init__(self, dist, f):
        self.dist = dist
        # build index of log entries
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
        # move to list for direct indexing
        maxpos = max(tmp)
        self._entries = (maxpos + 1) * [None]
        for k, v in tmp.iteritems():
            self._entries[k] = v

    def read(self, pos):
        address = self.dist.address(pos)
        tree, nbytes = self._entries[pos]
        return tree, nbytes, address

    def written_positions(self):
        snapshots = []
        for i in range(len(self._entries)):
            if self._entries[i] is not None:
                snapshots.append(i)
        return snapshots

class Database(object):
    def __init__(self, log, snapshot=None):
        self.log = log
        if snapshot is None:
            snapshot = -1
        tree, nbytes, addr = self.log.read(snapshot)
        self.root = tree[-1] if tree else None

        # stats
        self.total_resolves = 1
        self.remote_resolves = 1
        self.object_local_resolves = 0
        self.nbytes = nbytes
        self.last_address = addr

    def resolve(self, ptr):
        if ptr.nil:
            return None
        tree, nbytes, addr = self.log.read(ptr.pos)
        self.total_resolves += 1
        if addr == self.last_address:
            self.object_local_resolves += 1
        else:
            self.last_address = addr
            self.remote_resolves += 1
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

dist = LogDist(1)
log = Log(dist, sys.stdin)

writer = csv.writer(sys.stdout)
writer.writerow(("snapshot", "total_resolves", "remote_resolves",
            "object_local_resolves", "nbytes"))
snapshots = log.written_positions()
for snapshot in snapshots[-2:-1]:
    db = Database(log, snapshot)
    assert db.get(-1) is None
    writer.writerow((snapshot, db.total_resolves, db.remote_resolves,
                db.object_local_resolves, db.nbytes))
