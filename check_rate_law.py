#!/usr/bin/env python3
"""Verify the commutator rate law: ||pi1-pi2||_1 <= ||[A1,A2]||_inf / ((1-tau1)(1-tau2)).
1) Numeric: the seeded 123-config family from Fig 3 + fresh scrambling chains -> max ratio.
2) Identity checks: [A,B]1=0; pi2-pi1 = pi2(I-A1)Z1; ||pi2(I-A1)|| <= ||[A,B]||/(1-tau2).
3) Exact rational 3x3 spot check with Fractions."""
import numpy as np
from fractions import Fraction as F

def tau(A):  # Dobrushin coefficient
    n=A.shape[0]
    return 0.5*max(np.abs(A[i]-A[j]).sum() for i in range(n) for j in range(n))
def perron(A,it=20000):
    v=np.ones(A.shape[0])/A.shape[0]
    for _ in range(it): v=v@A; v/=v.sum()
    return v

rng=np.random.default_rng(0); worst=0.0; worst_id=0.0; m=0
for _ in range(200):
    n=int(rng.integers(8,30)); A=rng.random((n,n))+.05; A/=A.sum(1,keepdims=True)
    E=rng.normal(size=(n,n)); E-=E.mean(1,keepdims=True); t=10**rng.uniform(-4,-1.3)
    B=A+t*E
    if B.min()<=0: continue
    B/=B.sum(1,keepdims=True); m+=1
    C=A@B-B@A; cn=np.abs(C).sum(1).max()          # ||.||_inf as max abs row sum
    t1,t2=tau(A),tau(B)
    p1,p2=perron(A),perron(B)
    d=np.abs(p1-p2).sum()
    bound=cn/((1-t1)*(1-t2))
    worst=max(worst, d/bound)
    Z=np.linalg.inv(np.eye(n)-A+np.outer(np.ones(n),p1))
    lhs=p2-p1; rhs=(p2@(np.eye(n)-A))@Z
    worst_id=max(worst_id, np.abs(lhs-rhs).max())
    assert np.abs(p2@(np.eye(n)-A)).sum() <= cn/(1-t2)+1e-12
    assert np.abs(C.sum(1)).max()<1e-12            # commutator rows sum to zero
print(f"family: {m} configs | max ratio d/bound = {worst:.4f}  (<=1 required) | identity err {worst_id:.2e}")
assert worst <= 1.0+1e-9

worst2=0.0
for _ in range(300):
    n=int(rng.integers(3,15))
    A=rng.random((n,n))+.05; A/=A.sum(1,keepdims=True)
    B=rng.random((n,n))+.05; B/=B.sum(1,keepdims=True)
    C=A@B-B@A; cn=np.abs(C).sum(1).max()
    d=np.abs(perron(A)-perron(B)).sum()
    worst2=max(worst2, d/(cn/((1-tau(A))*(1-tau(B)))))
print(f"independent pairs: 300 configs | max ratio = {worst2:.4f}  (<=1 required)")
assert worst2 <= 1.0+1e-9

A=[[F(1,2),F(1,4),F(1,4)],[F(1,3),F(1,3),F(1,3)],[F(1,4),F(1,4),F(1,2)]]
Bm=[[F(2,5),F(2,5),F(1,5)],[F(1,5),F(3,5),F(1,5)],[F(1,3),F(1,3),F(1,3)]]
def mm(X,Y): return [[sum(X[i][k]*Y[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
Cm=[[mm(A,Bm)[i][j]-mm(Bm,A)[i][j] for j in range(3)] for i in range(3)]
assert all(sum(r)==0 for r in Cm), "commutator rows must sum to 0 exactly"
def stat(M):
    a,b,c=M[0],M[1],M[2]
    A11,A12,A13=a[0]-1,b[0],c[0]
    A21,A22,A23=a[1],b[1]-1,c[1]
    Mq=[[A11,A12,A13,F(0)],[A21,A22,A23,F(0)],[F(1),F(1),F(1),F(1)]]
    for col in range(3):
        piv=next(r for r in range(col,3) if Mq[r][col]!=0)
        Mq[col],Mq[piv]=Mq[piv],Mq[col]
        Mq[col]=[v/Mq[col][col] for v in Mq[col]]
        for r in range(3):
            if r!=col and Mq[r][col]!=0:
                f=Mq[r][col]; Mq[r]=[Mq[r][j]-f*Mq[col][j] for j in range(4)]
    return [Mq[r][3] for r in range(3)]
p1,p2=stat(A),stat(Bm)
assert all(sum(p1[i]*A[i][j] for i in range(3))==p1[j] for j in range(3))
assert all(sum(p2[i]*Bm[i][j] for i in range(3))==p2[j] for j in range(3))
d=sum(abs(p1[i]-p2[i]) for i in range(3))
cn=max(sum(abs(v) for v in r) for r in Cm)
tA=max(F(1,2)*sum(abs(A[i][k]-A[j][k]) for k in range(3)) for i in range(3) for j in range(3))
tB=max(F(1,2)*sum(abs(Bm[i][k]-Bm[j][k]) for k in range(3)) for i in range(3) for j in range(3))
bound=cn/((1-tA)*(1-tB))
print(f"exact 3x3: d={d} <= bound={bound}  ->", d<=bound)
assert d<=bound
print("RATE LAW VERIFIED: numeric (423 configs, two regimes) + exact rational, constant 1 never exceeded")

# ---- Sharpness: the two-state equality law (Prop) ----
# For 2x2 with off-diagonals (a_i,b_i), sigma_i=a_i+b_i:
#   ||pi1-pi2||_1 * sigma1*sigma2 == ||[A1,A2]||_inf  identically,
# so ratio-to-bound = gamma1*gamma2/(sigma1*sigma2) = 1 iff both sigma_i<=1 (lazy).
rng3=np.random.default_rng(1); worst_eq=0.0; worst_id2=0.0
def two(a,b): return np.array([[1-a,a],[b,1-b]])
for _ in range(2000):
    a1,b1,a2,b2 = rng3.uniform(0.01,0.99,4)
    A,B = two(a1,b1), two(a2,b2)
    C=A@B-B@A; cn=np.abs(C).sum(1).max()
    p1=np.array([b1,a1])/(a1+b1); p2=np.array([b2,a2])/(a2+b2)
    d=np.abs(p1-p2).sum()
    worst_id2=max(worst_id2, abs(d*(a1+b1)*(a2+b2)-cn))       # exact identity, float noise only
    s1,s2=a1+b1,a2+b2
    if s1<=1 and s2<=1:
        bound=cn/((1-abs(1-s1))*(1-abs(1-s2)))
        if cn>1e-12: worst_eq=max(worst_eq, abs(d-bound)/bound)
print(f"2x2 identity |d*s1*s2 - ||C|| | max = {worst_id2:.2e} | lazy-branch equality rel err max = {worst_eq:.2e}")
assert worst_id2 < 1e-12 and worst_eq < 1e-10

# exact rational 2x2, both branches
for (a1,b1,a2,b2) in [(F(1,4),F(1,4),F(1,10),F(3,10)), (F(7,10),F(4,5),F(3,5),F(9,10))]:
    s1,s2=a1+b1,a2+b2
    t=a1*b2-b1*a2; cn=2*abs(t)
    d=2*abs(t)/(s1*s2)
    g1,g2=1-abs(1-s1),1-abs(1-s2)
    bound=cn/(g1*g2)
    lazy = s1<=1 and s2<=1
    assert (d==bound) if lazy else (d<bound), (a1,b1,a2,b2)
print("exact 2x2: equality on the lazy branch, strict below on sigma>1 -- VERIFIED")

# ---- Problem 10.3 note: the idempotent lattice braiding (min,max) is braided, monotone, copy-free ----
def Rmm(x,y): return (min(x,y),max(x,y))
def R12(t): a,b=Rmm(t[0],t[1]); return (a,b,t[2])
def R23(t): a,b=Rmm(t[1],t[2]); return (t[0],a,b)
ok=0
for _ in range(300):
    tr=tuple(F(int(rng3.integers(0,100)),int(rng3.integers(1,100))) for _ in range(3))
    L=R12(R23(R12(tr))); R=R23(R12(R23(tr)))
    assert L==R==tuple(sorted(tr)); ok+=1
print(f"lattice sort braiding: braid relation exact on {ok}/300 rational triples; both sides = (min,med,max)")
print("SHARPNESS + 10.3 NOTE VERIFIED")

# ---- External benchmark: PageRank (Google) matrices on the Zachary karate club (public data) ----
# G = alpha*S + (1-alpha)*1 v^T is scrambling by construction: tau(G) <= alpha, so gamma >= 1-alpha.
KARATE_EDGES = [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,10),(0,11),(0,12),(0,13),(0,17),(0,19),(0,21),(0,31),(1,2),(1,3),(1,7),(1,13),(1,17),(1,19),(1,21),(1,30),(2,3),(2,7),(2,8),(2,9),(2,13),(2,27),(2,28),(2,32),(3,7),(3,12),(3,13),(4,6),(4,10),(5,6),(5,10),(5,16),(6,16),(8,30),(8,32),(8,33),(9,33),(13,33),(14,32),(14,33),(15,32),(15,33),(18,32),(18,33),(19,33),(20,32),(20,33),(22,32),(22,33),(23,25),(23,27),(23,29),(23,32),(23,33),(24,25),(24,27),(24,31),(25,31),(26,29),(26,33),(27,33),(28,31),(28,33),(29,32),(29,33),(30,32),(30,33),(31,32),(31,33),(32,33)]
nK = 34
AK = np.zeros((nK,nK))
for (u,v) in KARATE_EDGES: AK[u,v]=AK[v,u]=1.0
SK = AK/AK.sum(1,keepdims=True)
degK = AK.sum(1)
vsK = {"uniform": np.ones(nK)/nK, "hub": degK/degK.sum()}
import itertools as _it
worstK=0.0
for (a1,k1),(a2,k2) in _it.combinations([(a,k) for a in (0.85,0.90) for k in vsK],2):
    G1 = a1*SK + (1-a1)*np.outer(np.ones(nK), vsK[k1])
    G2 = a2*SK + (1-a2)*np.outer(np.ones(nK), vsK[k2])
    assert tau(G1) <= a1+1e-12 and tau(G2) <= a2+1e-12       # gamma >= 1-alpha, as claimed
    C=G1@G2-G2@G1; cn=np.abs(C).sum(1).max()
    if k1==k2=="hub": assert cn<1e-12, "hub-personalized Google matrices must commute (v = walk-stationary)"
    d=np.abs(perron(G1)-perron(G2)).sum()
    worstK=max(worstK, d/(cn/((1-tau(G1))*(1-tau(G2)))))
print(f"karate-club Google benchmark: 6 pairs, worst ratio = {worstK:.4f} (<=1 required)")
assert worstK <= 1.0
print("EXTERNAL BENCHMARK VERIFIED (public graph); hub-personalized pair commutes exactly: the zero locus, observed in the wild")
