#!/usr/bin/env python3
"""THE 3-LINE TEST: is YOUR merge rule order-dependent?

    from try_your_merge import order_drift
    drift = order_drift(my_fold)          # my_fold(state_or_None, item) -> state
    print("flat (order-proof)" if drift < 1e-9 else f"CURVED: drift {drift:.3f}")

Two instruments (Consensus Curvature, working draft):
  order_drift  -- holonomy defect of a fold: input FIXED, only the order varies.
                  0 <=> order-proof (Prop 3.4: commutative+idempotent suffices).
  braid_defect -- for pairwise meeting protocols R(x,y): Reidemeister-III
                  residual. Thm D: linear protocols are braided iff a scribe
                  keeps a verbatim copy; symmetric compromise defect = 1/8.
Design rule from the paper: a fold is flat iff every lossy step sits OUTSIDE it.
"""
import numpy as np

def order_drift(fold, n_inputs=200, n_orders=100, n_items=6, dist=None, item_gen=None, seed=11):
    rng=np.random.default_rng(seed)
    dist = dist or (lambda a,b: float(abs(a-b)))
    gen  = item_gen or (lambda: rng.random(n_items))
    worst=0.0
    for _ in range(n_inputs):
        items=gen(); finals=[]
        for _ in range(n_orders):
            st=None
            for k in rng.permutation(len(items)): st=fold(st,items[k])
            finals.append(st)
        for i in range(len(finals)):
            for j in range(i+1,len(finals)):
                worst=max(worst,dist(finals[i],finals[j]))
    return worst

def braid_defect(R, grid=26):
    """R: [0,1]^2 -> [0,1]^2 pairwise protocol. Returns sup Reidemeister-III residual."""
    def R12(v): x,y=R(v[0],v[1]); return (x,y,v[2])
    def R23(v): y,z=R(v[1],v[2]); return (v[0],y,z)
    ts=np.linspace(0,1,grid); w=0.0
    for x in ts:
        for y in ts:
            for z in ts:
                L=R12(R23(R12((x,y,z)))); Rr=R23(R12(R23((x,y,z))))
                w=max(w,max(abs(L[i]-Rr[i]) for i in range(3)))
    return w

if __name__=="__main__":
    print("== order_drift on standard folds (worst case over 200 fixed inputs) ==")
    demos={
     "running mean ": lambda s,v: (v,1) if s is None else (s[0]+(v-s[0])/(s[1]+1), s[1]+1),
     "max (CRDT)   ": lambda s,v: v if s is None else max(s,v),
     "EMA a=0.3    ": lambda s,v: v if s is None else 0.3*v+0.7*s,
     "sym average  ": lambda s,v: v if s is None else 0.5*v+0.5*s,
     "scribe/last  ": lambda s,v: v,
    }
    dists={"running mean ": lambda a,b: abs(a[0]-b[0])}
    for name,f in demos.items():
        d=order_drift(f,dist=dists.get(name))
        print(f"  {name}: drift {d:.3e}  -> {'FLAT (order-proof)' if d<1e-9 else 'CURVED'}")
    print("\n== braid_defect on linear meeting protocols R(x,y)=((1-a)x+ay, bx+(1-b)y) ==")
    for name,(a,b) in {"symmetric 1/2":(.5,.5),"scribe a=1":(1,.5),"swap":(1,1),"generic .3/.6":(.3,.6)}.items():
        d=braid_defect(lambda x,y,a=a,b=b: ((1-a)*x+a*y, b*x+(1-b)*y))
        print(f"  {name:14s}: {d:.6f}" + ("   <- exactly 1/8, Cor 6.2" if abs(d-0.125)<1e-9 else ""))
    print("\nYour turn: import order_drift, hand it your fold. Verdict in one number.")
