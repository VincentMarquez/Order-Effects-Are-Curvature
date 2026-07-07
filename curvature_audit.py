#!/usr/bin/env python3
"""
curvature_audit.py
==================
A "consensus-curvature" auditor for information/agent networks.

Reads a graph JSON (nodes + edges), treats it as an aggregation network
(Consensus Curvature framework, Theorem A), and reports:

  * FLAT vs CURVATURE-CAPABLE
      FLAT (a "multitree": no directed cycles AND at most one directed path
      between any ordered pair) => NO choice of merge/aggregation rules can
      ever make a result depend on execution order. Safe by shape.
      Otherwise => route/order dependence is POSSIBLE; which rule you pick
      now matters.

  * directed cycles (feedback loops) via Tarjan SCC
  * "diamond" pairs: ordered (s,t) with >= 2 distinct directed routes
  * ranked MERGE junctions: where many routes converge (the places where the
    order in which inputs are combined can change the output)
  * ranked BRANCH points: where routes split

Accepts flexible schemas:
  nodes: [{"id"/"name", "type"?, ...}]
  edges/links: [{"source"/"from", "target"/"to", "relation"?}]

Usage:
  python3 curvature_audit.py your_graph.json
  python3 curvature_audit.py graphA.json graphB.json --top 15

Notes:
  - Multi-edges and self-loops are handled. Path counts on the condensation
    DAG are saturated at 2 (we only need "is there more than one route"),
    so the audit is linear-ish and scales to large graphs.
  - This flags STRUCTURAL possibility of order-dependence. Whether a given
    junction ACTUALLY drifts depends on the merge rule there: idempotent or
    scribe-style merges are safe even at a diamond (see the framework's
    Theorem D and the idempotent proposition).

Part of the consensus_curvature project. Machine-verified framework; the
underlying theorems are working-draft (not peer reviewed).
"""

import json
import sys
import pathlib
from collections import defaultdict


def load_graph(path):
    obj = json.loads(pathlib.Path(path).read_text())
    nodes = obj.get('nodes', [])
    edges_raw = obj.get('edges', obj.get('links', []))
    ids, meta = [], {}
    for nd in nodes:
        nid = nd.get('id', nd.get('name'))
        if nid not in meta:
            ids.append(nid)
        meta[nid] = nd
    E = []
    for e in edges_raw:
        u = e.get('source', e.get('from'))
        v = e.get('target', e.get('to'))
        if u is None or v is None:
            continue
        E.append((u, v, e.get('relation', e.get('label', ''))))
        for w in (u, v):
            if w not in meta:
                ids.append(w)
                meta[w] = {'id': w}
    return ids, meta, E


def tarjan_scc(ids, adj):
    """Iterative Tarjan; returns list of SCCs (each a list of node ids)."""
    index, low, onstk = {}, {}, {}
    stk, sccs, counter = [], [], [0]
    for root in ids:
        if root in index:
            continue
        work = [(root, iter(adj[root]))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stk.append(root)
        onstk[root] = True
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stk.append(w)
                    onstk[w] = True
                    work.append((w, iter(adj[w])))
                    advanced = True
                    break
                elif onstk.get(w):
                    low[v] = min(low[v], index[w])
            if not advanced:
                work.pop()
                if work:
                    u = work[-1][0]
                    low[u] = min(low[u], low[v])
                if low[v] == index[v]:
                    scc = []
                    while True:
                        w = stk.pop()
                        onstk[w] = False
                        scc.append(w)
                        if w == v:
                            break
                    sccs.append(scc)
    return sccs


def audit(path, top=10, label=''):
    ids, meta, E = load_graph(path)
    adj = defaultdict(list)
    for u, v, r in E:
        adj[u].append(v)
    n, m = len(ids), len(E)

    sccs = tarjan_scc(ids, adj)
    big = [s for s in sccs if len(s) > 1]
    scc_of = {v: i for i, s in enumerate(sccs) for v in s}

    cadj = defaultdict(set)
    for u, v, r in E:
        if scc_of[u] != scc_of[v]:
            cadj[scc_of[u]].add(scc_of[v])
    C = len(sccs)
    indeg = [0] * C
    for u in cadj:
        for v in cadj[u]:
            indeg[v] += 1
    topo = [i for i in range(C) if indeg[i] == 0]
    ind, head = indeg[:], 0
    while head < len(topo):
        u = topo[head]
        head += 1
        for v in cadj[u]:
            ind[v] -= 1
            if ind[v] == 0:
                topo.append(v)

    merge_score = defaultdict(int)
    branch_score = defaultdict(int)
    diamonds = 0
    for s in range(C):
        cnt = [0] * C
        cnt[s] = 1
        for u in topo:
            if cnt[u] == 0:
                continue
            for v in cadj[u]:
                cnt[v] = min(2, cnt[v] + cnt[u])
        for t in range(C):
            if t != s and cnt[t] >= 2:
                diamonds += 1
                merge_score[t] += 1
                branch_score[s] += 1

    def name(ci):
        rep = sccs[ci][0]
        nd = meta.get(rep, {})
        return f"{nd.get('name', rep)} [{nd.get('type', '?')}]"

    cyc_nodes = sum(len(s) for s in big)
    flat = (not big) and diamonds == 0

    print(f"===== CURVATURE AUDIT: {label or path} =====")
    print(f"nodes={n}  edges={m}  (a tree on these nodes would have {max(n-1,0)} "
          f"edges; surplus = {m - max(n-1, 0)})")
    if flat:
        print("VERDICT: FLAT (multitree) -- no ordering of merges can EVER "
              "change a result (Theorem A).")
    else:
        print("VERDICT: CURVATURE-CAPABLE -- route/order dependence is "
              "POSSIBLE; the merge rule now matters (Theorem A).")
    if big:
        print(f"directed cycles: {len(big)} nontrivial SCC(s) covering "
              f"{cyc_nodes} nodes -> e.g. "
              f"{[meta.get(v, {}).get('name', v) for v in big[0][:6]]}")
    else:
        print("directed cycles: none")
    print(f"diamond pairs (ordered s,t with >=2 distinct routes): {diamonds}")

    if merge_score:
        print("\nTop MERGE junctions (routes converge -> order of aggregation "
              "can matter here):")
        for ci, sc in sorted(merge_score.items(), key=lambda kv: -kv[1])[:top]:
            ins = [(meta.get(u, {}).get('name', u), r)
                   for u, v, r in E if scc_of[v] == ci]
            print(f"  {sc:5d} route-pairs converge at {name(ci)}")
            for src, rel in ins[:4]:
                print(f"          <- {src}  ({rel})")
    if branch_score:
        print("\nTop BRANCH points (routes split here):")
        for ci, sc in sorted(branch_score.items(), key=lambda kv: -kv[1])[:5]:
            print(f"  {sc:5d} route-pairs originate at {name(ci)}")
    print("\nGuidance: to make any flagged junction order-proof, use an "
          "idempotent merge (f(f)=f, CRDT-style) or a scribe rule (one input "
          "copied verbatim). Symmetric 50/50 merges can never be made "
          "order-proof (Theorem D).\n")
    return {'flat': flat, 'nodes': n, 'edges': m, 'cycles': len(big),
            'diamonds': diamonds}


def main(argv):
    top = 10
    files, skip = [], False
    for i, a in enumerate(argv):
        if skip:
            skip = False
            continue
        if a.startswith('--top='):
            try:
                top = int(a.split('=', 1)[1])
            except Exception:
                pass
        elif a == '--top':
            if i + 1 < len(argv):
                try:
                    top = int(argv[i + 1])
                except Exception:
                    pass
                skip = True
        elif a.startswith('--'):
            continue
        else:
            files.append(a)
    if not files:
        print(__doc__)
        return
    for path in files:
        audit(path, top=top, label='')


if __name__ == '__main__':
    main(sys.argv[1:])
