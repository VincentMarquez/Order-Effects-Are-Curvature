#!/usr/bin/env python3
"""S8.5 load-bearing numerics, independent re-implementation (fresh code, fixed seeds).
1) Perron-vector distance vs commutator norm: predict log-log slope ~1 (rate half of Problem 10.4).
2) Truncation placement: deferred time-KL flat (~1e-15) vs streaming rank-K curved (>0.05)."""
import numpy as np, json
from scipy import stats
rng=np.random.default_rng(0)
def perron(A,it=8000):
    v=np.ones(A.shape[0])/A.shape[0]
    for _ in range(it): v=v@A; v/=v.sum()
    return v
xs,ys=[],[]
for _ in range(200):
    n=int(rng.integers(8,30)); A=rng.random((n,n))+.05; A/=A.sum(1,keepdims=True)
    E=rng.normal(size=(n,n)); E-=E.mean(1,keepdims=True); t=10**rng.uniform(-4,-1.3)
    B=A+t*E
    if B.min()<=0: continue
    B/=B.sum(1,keepdims=True)
    c=np.linalg.norm(A@B-B@A,2); d=np.abs(perron(A)-perron(B)).sum()
    if c>0 and d>0: xs.append(np.log(c)); ys.append(np.log(d))
slope=float(np.polyfit(xs,ys,1)[0]); sp=float(stats.spearmanr(xs,ys).statistic)
T,dm,K=40,12,4; X0=rng.normal(size=(T,dm))
def deferred(X):
    Kt=X@X.T; w,U=np.linalg.eigh(Kt); U=U[:,np.argsort(-w)[:K]]
    M=X.T@U; return M@np.linalg.pinv(M)
def streaming(X):
    B=None
    for x in X:
        B=x[None] if B is None else np.vstack([B,x[None]])
        if B.shape[0]>K:
            u,s,vt=np.linalg.svd(B,full_matrices=False); B=((u[:,:K]*s[:K])@vt[:K])[:K]
    return B.T@np.linalg.pinv(B.T)
def drift(fn):
    Ps=[fn(X0[rng.permutation(T)]) for _ in range(60)]
    return max(np.linalg.norm(Ps[0]-P) for P in Ps[1:])
dA,dS=drift(deferred),drift(streaming)
ok = 0.9<=slope<=1.1 and sp>0.97 and dA<1e-10 and dS>0.05
print(f"Perron/commutator: slope {slope:.3f} Spearman {sp:.3f} (predict ~1.0)")
print(f"placement: deferred {dA:.1e} vs streaming {dS:.3f} (ratio {dS/max(dA,1e-300):.1e})")
print("PASS" if ok else "FAIL")
json.dump(dict(slope=slope,spearman=sp,deferred=dA,streaming=dS,gate='PASS' if ok else 'FAIL'),
          open(__file__.replace('adoption_reverify.py','../adoption_reverify_result.json'),'w'),indent=2)
