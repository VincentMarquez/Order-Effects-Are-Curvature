
import numpy as np, torch, ast, json
from scipy import stats
import scipy.linalg as sla
from transformers import AutoModel, AutoTokenizer
DEV="cuda"
src=open("replicate_depth_controlled.py").read()
tree=ast.parse(src); PROMPTS=None
for node in tree.body:
    if isinstance(node,ast.Assign) and getattr(node.targets[0],"id","")=="PROMPTS":
        PROMPTS=ast.literal_eval(node.value)
assert len(PROMPTS)==50

def specnorm(C):
    try: return float(np.linalg.norm(C,2))
    except Exception: return float(sla.svdvals(C)[0])

def series(m,tok,text):
    enc=tok(text,return_tensors="pt",truncation=True,max_length=64).to(DEV)
    with torch.no_grad(): out=m(**enc,output_attentions=True,output_hidden_states=True)
    A=[a[0].mean(0).float().cpu().numpy() for a in out.attentions]
    integ={"finite":all(np.isfinite(x).all() for x in A),
           "rowsum_maxdev":max(float(np.abs(x.sum(1)-1).max()) for x in A)}
    if not integ["finite"]: return None,integ
    H=[h[0].float().cpu().numpy() for h in out.hidden_states]; L=len(A)
    c=np.array([specnorm(A[l]@A[l+1]-A[l+1]@A[l]) for l in range(L-1)])
    def clu(X):
        Xn=X/(np.linalg.norm(X,axis=1,keepdims=True)+1e-9); S=Xn@Xn.T
        iu=np.triu_indices(X.shape[0],1); return float(S[iu].mean())
    C=np.array([clu(H[l]) for l in range(L+1)])
    return (c,C[1:]-C[:-1],L),integ

def psp(x,y,z):
    rx,ry,rz=(stats.rankdata(v) for v in (x,y,z))
    def res(a,b):
        B=np.c_[np.ones_like(b),b]; be,*_=np.linalg.lstsq(B,a,rcond=None); return a-B@be
    ex,ey=res(rx,rz),res(ry,rz)
    return float(stats.spearmanr(ex,ey).statistic) if ex.std()>1e-9 and ey.std()>1e-9 else np.nan
def pspf(x,y,z):
    rxy=stats.spearmanr(x,y).statistic; rxz=stats.spearmanr(x,z).statistic; ryz=stats.spearmanr(y,z).statistic
    den=np.sqrt((1-rxz**2)*(1-ryz**2)); return float((rxy-rxz*ryz)/den) if den>1e-9 else np.nan

RES={}
for name,hf in [("gpt2","gpt2"),("pythia-160m","EleutherAI/pythia-160m"),("pythia-410m","EleutherAI/pythia-410m")]:
    tok=AutoTokenizer.from_pretrained(hf)
    m=AutoModel.from_pretrained(hf,attn_implementation="eager").to(DEV).eval()
    rows={k:[] for k in ["A1_asrun","A1_formula","A2_shift","A3_pairsum","A4_dropfirst"]}
    bad=0; maxdev=0.0
    for text in PROMPTS:
        s,integ=series(m,tok,text)
        maxdev=max(maxdev,integ["rowsum_maxdev"] if integ["finite"] else 0)
        if s is None: bad+=1; continue
        c,g,L=s; d=np.arange(L-1,dtype=float)
        rows["A1_asrun"].append(psp(c,g[:L-1],d))
        rows["A1_formula"].append(pspf(c,g[:L-1],d))
        rows["A2_shift"].append(psp(c,g[1:L],d))
        rows["A3_pairsum"].append(psp(c,g[:L-1]+g[1:L],d))
        rows["A4_dropfirst"].append(psp(c[1:],g[1:L-1],d[1:]))
    del m; torch.cuda.empty_cache()
    out={"nan_prompts":bad,"rowsum_maxdev":maxdev}
    print(f"### {name}: NaN-skipped {bad}/50, row-stochastic maxdev {maxdev:.1e}")
    for k,v in rows.items():
        v=np.array([x for x in v if np.isfinite(x)])
        p=float(stats.wilcoxon(v,alternative="less").pvalue) if len(v)>5 and np.any(v!=0) else float("nan")
        out[k]=dict(median=float(np.median(v)),frac_neg=float((v<0).mean()),p_less=p,n=len(v))
        print(f"  {k:12s}: {out[k][chr(109)+chr(101)+chr(100)+chr(105)+chr(97)+chr(110)]:+.3f} | frac<0 {out[k][chr(102)+chr(114)+chr(97)+chr(99)+chr(95)+chr(110)+chr(101)+chr(103)]:.2f} | p={p:.1e} | n={len(v)}")
    RES[name]=out
json.dump(RES,open("audit_system_env.json","w"),indent=2)
print("saved audit_system_env.json")
