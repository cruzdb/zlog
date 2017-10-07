import sys
from graphviz import Digraph
import kvs

log = kvs.Log(sys.stdin)
snapshots = log.snapshots()

for snapshot in snapshots[0:1000]:
    u = Digraph(`snapshot`.zfill(8), format="png",
            graph_attr={'ratio': 'fill',
                        'size': '15,10'},
            node_attr={'fontcolor': 'white'})
    db = kvs.Database(log, 1, snapshot)
    for node in db.preorder():
        u.node(node.address(), label=`int(node.key)`,
                style='filled',
                color='red' if node.red else 'black')
        if not node.left.nil: u.edge(node.address(), node.left.address())
        if not node.right.nil: u.edge(node.address(), node.right.address())
    u.render()
