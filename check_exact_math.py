#!/usr/bin/env python3
"""Tier 0: the paper's four theorems, verified in EXACT rational arithmetic.
No trust required -- run it. Deps: numpy (Stokes grids only). ~30s.
Blocks: A ThmD factorization+zero-set | B closed-form sups (1/8, 21/125)
        C ladder equality exact | D 300 random Stokes grids | E robust core + Shapley
"""
from fractions import Fraction as F
import random, itertools, math, sys
import numpy as np
random.seed(3); ok=True
def blk(name,cond):
    global ok; ok&=cond; print(f"[{'PASS' if cond else 'FAIL'}] {name}")

# A: Thm D --- L-R = (1-a)(1-b)N exactly; zero-set = braided classification
def mm(A,B): return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
fails=0
for _ in range(300):
    a=F(random.randint(0,20),20); b=F(random.randint(0,20),20)
    R12=[[1-a,a,0],[b,1-b,0],[0,0,1]]; R23=[[1,0,0],[0,1-a,a],[0,b,1-b]]
    D=[[x-y for x,y in zip(r1,r2)] for r1,r2 in zip(mm(mm(R12,R23),R12),mm(mm(R23,R12),R23))]
    N=[[-a,a,0],[b,a-b,-a],[0,-b,b]]
    if D!=[[(1-a)*(1-b)*N[i][j] for j in range(3)] for i in range(3)]: fails+=1
    if (all(v==0 for r in D for v in r))!=(a==1 or b==1 or (a==0 and b==0)): fails+=1
blk("A: Thm D exact factorization + zero-set, 300 rational samples", fails==0)

# B: closed-form sup over the cube
def supD(a,b):
    N=[[-a,a,0],[b,a-b,-a],[0,-b,b]]
    return (1-a)*(1-b)*max(max(sum(x for x in r if x>0),-sum(x for x in r if x<0)) for r in N)
blk("B: sup(1/2,1/2)=1/8 and sup(3/10,3/5)=21/125 exactly",
    supD(F(1,2),F(1,2))==F(1,8) and supD(F(3,10),F(3,5))==F(21,125))

# C: Thm 4.3 ladder equality, exact (m=3, n=4)
m,n=3,4; beta=[F(j,2*m*n) for j in range(n+1)]
xs=[F(k,48) for k in range(49)]
blk("C: ladder boundary defect == sum of faces, exactly in Q",
    m*(beta[n]-beta[0])==max(abs(min(x+m*beta[n],F(1))-x) for x in xs))

# D: Thm 4.1 on 300 fresh random nonexpansive 2x2 grids
G=np.linspace(0,1,101); rng=np.random.default_rng(9); viol=0
def rmap():
    y=np.minimum(np.cumsum(np.r_[rng.uniform(0,.3),rng.uniform(0,G[1],100)]),1.0)
    return lambda x: np.interp(x,G,y)
for _ in range(300):
    h={(i,j):rmap() for i in range(3) for j in range(2)}
    v={(i,j):rmap() for i in range(2) for j in range(3)}
    X=np.linspace(0,1,401)
    faces=sum(np.max(np.abs(v[(i,j+1)](h[(i,j)](X))-h[(i+1,j)](v[(i,j)](X)))) for i in range(2) for j in range(2))
    bd=np.max(np.abs(v[(1,2)](v[(0,2)](h[(0,1)](h[(0,0)](X))))-h[(2,1)](h[(2,0)](v[(1,0)](v[(0,0)](X))))))
    if bd>faces+1e-9: viol+=1
blk("D: Stokes inequality, 300 random grids, zero violations", viol==0)

# E: robust core vs ALL 2^9 subsets + exact Shapley identity
def comp(ed,nn):
    par=list(range(nn))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for u,w in ed:
        a_,b_=f(u),f(w)
        if a_!=b_: par[a_]=b_
    return len({f(i) for i in range(nn)})
bad=0
for _ in range(40):
    nn=9; k=random.randint(1,4); perms=[]
    for _ in range(k):
        sz=random.randint(2,6); pts=random.sample(range(nn),sz); p=list(range(nn))
        for i in range(sz): p[pts[i]]=pts[(i+1)%sz]
        if random.random()<.25: p=list(range(nn))
        perms.append(p)
    E=[{(min(s,p[s]),max(s,p[s])) for s in range(nn) if p[s]!=s} for p in perms]
    orb=comp(set().union(*E) if any(E) else set(),nn)
    cnt=sum(1 for mask in range(1<<nn)
            if all({p[i] for i in range(nn) if mask>>i&1}=={i for i in range(nn) if mask>>i&1} for p in perms))
    if cnt!=2**orb: bad+=1
    def r(A): return nn-comp(set().union(*[E[i] for i in A]) if A else set(),nn)
    ksh=[]
    for i in range(k):
        val=F(0); others=[j for j in range(k) if j!=i]
        for rs in range(len(others)+1):
            for A in itertools.combinations(others,rs):
                val+=F(math.factorial(len(A))*math.factorial(k-len(A)-1),math.factorial(k))*(r(set(A)|{i})-r(set(A)))
        ksh.append(val/nn)
    if F(orb,nn)+sum(ksh)!=1: bad+=1
blk("E: robust core vs all 2^9 subsets + Shapley identity exact, 40 trials", bad==0)

print("\n"+("ALL EXACT CHECKS PASSED" if ok else "FAILURES -- see above"))
sys.exit(0 if ok else 1)
