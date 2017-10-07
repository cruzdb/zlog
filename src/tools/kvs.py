import json

class LogDist(object):
    __slots__ = ('nobjs')

    def __init__(self, nobjs):
        self.nobjs = nobjs

    def address(self, pos):
        oid = pos % self.nobjs
        return oid

class NodePointer(object):
    """A tree node pointer.

    The `same` property is true when the log position of the target node is
    contained in the same snapshot as the source node. In this case the `pos`
    parameter of the constructor is the target log position. Otherwise, the log
    position of the target node is provided by the `csn` property of the
    pointer. The `off` property is the position in the snapshot of the target node.
    """
    __slots__ = ('nil', 'same', 'pos', 'off')

    def __init__(self, pos, ptr):
        self.nil = bool(ptr["nil"])
        self.same = bool(ptr["self"])
        if self.same:
            self.pos = int(pos)
        else:
            self.pos = int(ptr["csn"])
        self.off = int(ptr["off"])

    def address(self):
        if self.nil:
            return None
        return "%d.%d" % (self.pos, self.off)

    def __repr__(self):
        if self.nil:
            return "nil"
        elif self.same:
            return "s%d:%d" % (self.pos, self.off)
        else:
            return "%d:%d" % (self.pos, self.off)

class Node(object):
    """A red-black tree node.

    The node is red if `red` is true, otherwise it is black. The left and
    right children are provided by the `left` and `right` fields.
    """
    __slots__= ('key', 'val', 'red', 'left', 'right', 'pos', 'off')

    def __init__(self, pos, offset, node):
        self.key = node["key"]
        self.val = node["val"]
        self.red = node["red"]
        self.left = NodePointer(pos, node["left"])
        self.right = NodePointer(pos, node["right"])
        self.pos = pos
        self.off = offset

    def address(self):
        return "%d.%d" % (self.pos, self.off)

    def __repr__(self):
        return "%s/%s/%s" % (self.key, self.left, self.right)

class Log(object):
    __slots__ = ('_entries')

    def __init__(self, f):
        # read the trace file and build an index
        tmp = {}
        for line in f.xreadlines():
            entry = json.loads(line)
            pos = entry["pos"]
            assert pos not in tmp
            nodes = []
            offset = 0
            for node in entry["tree"]:
                n = Node(pos, offset, node)
                nodes.append(n)
                offset += 1
            tmp[pos] = (nodes, entry["bytes"])

        # rebuild for direct indexing
        maxpos = max(tmp)
        self._entries = (maxpos + 1) * [None]
        for k, v in tmp.iteritems():
            self._entries[k] = v

    def read(self, pos, dist):
        address = dist.address(pos)
        tree, nbytes = self._entries[pos]
        return tree, nbytes, address

    def latest_snapshot(self):
        return self.snapshots()[-1]

    def snapshots(self):
        snapshots = []
        for i in range(len(self._entries)):
            if self._entries[i] is not None:
                snapshots.append(i)
        return snapshots

class Database(object):
    def __init__(self, log, width, snapshot=None):
        self.log = log
        self.dist = LogDist(width)
        self.snapshot = snapshot if snapshot is not None else -1

    def _get_snapshot(self):
        tree, nbytes, addr = self.log.read(self.snapshot, self.dist)
        return (tree[-1], addr) if tree else (None, None)

    def _resolve(self, ptr):
        if ptr.nil:
            return None, None
        tree, nbytes, addr = self.log.read(ptr.pos, self.dist)
        return tree[ptr.off], addr

    def keys(self):
        stack = []
        node, _ = self._get_snapshot()
        while len(stack) > 0 or node:
            if node:
                stack.append(node)
                node, _ = self._resolve(node.left)
            else:
                node = stack.pop()
                yield node.key
                node, _ = self._resolve(node.right)

    def path(self, key):
        path = []
        curr, addr = self._get_snapshot()
        while curr:
            path.append((curr, addr))
            if curr.key == key:
                return path
            elif curr.key > key:
                curr, addr = self._resolve(curr.left)
            else:
                curr, addr = self._resolve(curr.right)
        return None

    def paths(self):
        for key in self.keys():
            yield self.path(key)

    def get(self, key):
        curr, _ = self._get_snapshot()
        while curr:
            if curr.key == key:
                return curr.val
            elif curr.key > key:
                curr, _ = self._resolve(curr.left)
            else:
                curr, _ = self._resolve(curr.right)
        return None

    def preorder(self):
        node, _ = self._get_snapshot()
        if not node:
            return
        stack = []
        stack.append(node)
        while stack:
            node = stack.pop()
            yield node
            left, _ = self._resolve(node.left)
            if left: stack.append(left)
            right, _ = self._resolve(node.right)
            if right: stack.append(right)
