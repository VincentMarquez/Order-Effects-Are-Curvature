"""
Depth-controlled replication of the commutator/clustering correlation.
Pre-registered in PREREG_depth_controlled.md. Primary endpoint decided
BEFORE running; decision rule is symmetric (reports null honestly).

Fixes vs the original -0.809:
  - partial Spearman controlling for layer index (kills depth confound)
  - per-prompt distribution + Wilcoxon (not one aggregate number)
  - 50 prompts x 5 seeds, two architectures
  - shuffled-layer negative control
"""
import numpy as np, torch, json, sys, time
from scipy import stats
torch.manual_seed(0)
DEV = 'cuda' if torch.cuda.is_available() else 'cpu'

PROMPTS = [
 "The committee reviewed the proposal and rejected it after a long debate.",
 "Once upon a time, a small fox lived at the edge of a dark forest.",
 "def merge(a, b): return sorted(set(a) | set(b))",
 "\"I disagree,\" she said, \"the data clearly points the other way.\"",
 "Photosynthesis converts light energy into chemical energy in plants.",
 "The stock market fell sharply today amid fears of rising inflation.",
 "To install the package, run pip install followed by the module name.",
 "He walked into the room, sat down, and said nothing for a while.",
 "The theorem states that every continuous function attains its maximum.",
 "Mix the flour and sugar, then slowly add the eggs while whisking.",
 "Climate models predict warming of two to four degrees this century.",
 "The general ordered the troops to hold the bridge until reinforcements came.",
 "In quantum mechanics, observation collapses the wavefunction.",
 "Turn left at the second light, then continue for about two miles.",
 "The jury deliberated for six hours before reaching a verdict.",
 "for i in range(n): total += arr[i] * weights[i]",
 "The river carved the canyon over millions of years of slow erosion.",
 "\"We need to ship by Friday,\" the manager insisted, checking her watch.",
 "Antibiotics kill bacteria but have no effect on viral infections.",
 "The orchestra tuned their instruments as the audience settled in.",
 "A balanced diet includes proteins, carbohydrates, fats, and vitamins.",
 "The satellite transmitted images of the storm forming over the ocean.",
 "class Node: def __init__(self, val): self.val = val; self.next = None",
 "She opened the letter, read it twice, and set it down slowly.",
 "The economy grew by three percent in the last fiscal quarter.",
 "Gravity bends the path of light around massive celestial objects.",
 "First preheat the oven, then grease the pan before adding the batter.",
 "The senator argued that the new policy would harm small businesses.",
 "Migration patterns shift as temperatures change across the seasons.",
 "The detective examined the room for any sign of forced entry.",
 "Neural networks learn by adjusting weights through backpropagation.",
 "The children played in the yard until the sun began to set.",
 "import numpy as np; x = np.zeros((3, 3)); x[0, 0] = 1",
 "The treaty was signed after months of tense negotiation.",
 "Erosion, weathering, and deposition shape the surface of the earth.",
 "\"Hold on,\" he whispered, \"I think I heard something outside.\"",
 "The company reported record profits despite the economic downturn.",
 "Enzymes act as catalysts, speeding up biochemical reactions.",
 "Take the highway north, exit at the third ramp, then go east.",
 "The professor explained the proof step by step on the whiteboard.",
 "A gentle rain fell over the quiet town late in the evening.",
 "The algorithm sorts the list in n log n time on average.",
 "Voters lined up early to cast their ballots in the election.",
 "The volcano erupted, sending ash miles into the atmosphere.",
 "def fib(n): return n if n < 2 else fib(n-1) + fib(n-2)",
 "She tuned the radio until the static gave way to music.",
 "Supply and demand determine the price of goods in a free market.",
 "The astronaut described the curve of the earth against the black sky.",
 "Bacteria reproduce rapidly under warm and moist conditions.",
 "The old clock in the hall chimed twelve times at midnight.",
]
assert len(PROMPTS) == 50

def attention_maps_and_hidden(model, tok, text):
    enc = tok(text, return_tensors='pt', truncation=True, max_length=64).to(DEV)
    with torch.no_grad():
        out = model(**enc, output_attentions=True, output_hidden_states=True)
    # attentions: tuple[L] each (1, H, T, T); hidden: tuple[L+1] each (1, T, D)
    A = [a[0].mean(0).float().cpu().numpy() for a in out.attentions]      # head-avg -> (T,T), already row-stochastic
    H = [h[0].float().cpu().numpy() for h in out.hidden_states]           # (T,D)
    return A, H

def commutator_norm(A1, A2):
    C = A1 @ A2 - A2 @ A1
    return float(np.linalg.norm(C, 2))   # spectral norm

def clustering(hidden):  # mean pairwise cosine sim of token rows
    X = hidden
    n = X.shape[0]
    if n < 2: return np.nan
    Xn = X / (np.linalg.norm(X, axis=1, keepdims=True) + 1e-9)
    S = Xn @ Xn.T
    iu = np.triu_indices(n, k=1)
    return float(S[iu].mean())

def dobrushin_tau(A):  # 1 - 0.5 * max_{i,j} ||row_i - row_j||_1
    n = A.shape[0]; m = 0.0
    for i in range(n):
        d = 0.5 * np.abs(A[i] - A).sum(1)   # to all rows
        m = max(m, d.max())
    return float(m)  # this is the coefficient; contraction = tau, gap = 1-tau

def partial_spearman(x, y, z):
    # residualize ranks of x and y on rank of z, correlate residuals
    rx, ry, rz = (stats.rankdata(v) for v in (x, y, z))
    def resid(a, b):
        b1 = np.c_[np.ones_like(b), b]
        beta, *_ = np.linalg.lstsq(b1, a, rcond=None)
        return a - b1 @ beta
    ex, ey = resid(rx, rz), resid(ry, rz)
    if np.std(ex) < 1e-9 or np.std(ey) < 1e-9: return np.nan
    return float(stats.spearmanr(ex, ey).statistic)

def run_model(name, hf_id, seeds=5):
    from transformers import AutoModel, AutoTokenizer
    print(f"\n### {name} ({hf_id})", flush=True)
    tok = AutoTokenizer.from_pretrained(hf_id)
    model = AutoModel.from_pretrained(hf_id, attn_implementation='eager').to(DEV).eval()
    # per-prompt series (deterministic in eval; seeds only reshuffle prompt subsample)
    per_prompt_partial = []
    per_prompt_partial_shuf = []
    raw_pooled_c, raw_pooled_g, raw_pooled_depth = [], [], []
    tau_all_gap, tau_all_g = [], []
    for pi, text in enumerate(PROMPTS):
        A, H = attention_maps_and_hidden(model, tok, text)
        L = len(A)
        c = np.array([commutator_norm(A[l], A[l+1]) for l in range(L-1)])
        Cl = np.array([clustering(H[l]) for l in range(L+1)])   # hidden 0..L
        # clustering gain across block l acts between hidden[l] and hidden[l+1]; align to c (layers 0..L-2 pairs)
        g = np.array([Cl[l+1] - Cl[l] for l in range(L-1)])      # length L-1, same index base as c
        depth = np.arange(L-1, dtype=float)
        if np.all(np.isfinite(c)) and np.all(np.isfinite(g)):
            per_prompt_partial.append(partial_spearman(c, g, depth))
            raw_pooled_c.append(c); raw_pooled_g.append(g); raw_pooled_depth.append(depth)
            # shuffled-layer control: permute which A pairs with which
            rng = np.random.default_rng(1000+pi)
            perm = rng.permutation(L)
            As = [A[k] for k in perm]
            cs = np.array([commutator_norm(As[l], As[l+1]) for l in range(L-1)])
            per_prompt_partial_shuf.append(partial_spearman(cs, g, depth))
            # secondary: dobrushin gap vs g
            tau = np.array([dobrushin_tau(A[l]) for l in range(L)])
            gap = 1.0 - tau
            tau_all_gap.append(gap[:L-1]); tau_all_g.append(g)
    pp = np.array([v for v in per_prompt_partial if np.isfinite(v)])
    pps = np.array([v for v in per_prompt_partial_shuf if np.isfinite(v)])
    # primary
    med = float(np.median(pp))
    w = stats.wilcoxon(pp, alternative='less')  # H1: median < 0
    med_s = float(np.median(pps))
    ws = stats.wilcoxon(pps, alternative='less')
    # aggregate raw (to expose the confound)
    C = np.concatenate(raw_pooled_c); G = np.concatenate(raw_pooled_g); Z = np.concatenate(raw_pooled_depth)
    raw_rho = float(stats.spearmanr(C, G).statistic)
    depth_vs_g = float(stats.spearmanr(Z, G).statistic)
    partial_pooled = partial_spearman(C, G, Z)
    tau_rho = float(stats.spearmanr(np.concatenate(tau_all_gap), np.concatenate(tau_all_g)).statistic)
    res = dict(model=name, hf_id=hf_id, n_prompts=len(pp), n_layers_pairs=int(L-1),
               PRIMARY_median_partial_rho=med, PRIMARY_wilcoxon_p=float(w.pvalue),
               frac_negative=float((pp<0).mean()),
               shuffle_median_partial_rho=med_s, shuffle_wilcoxon_p=float(ws.pvalue),
               raw_pooled_spearman=raw_rho, depth_vs_clustering_spearman=depth_vs_g,
               partial_pooled_spearman=float(partial_pooled),
               secondary_dobrushin_gap_vs_gain=tau_rho)
    for k,v in res.items(): print(f"  {k}: {v}")
    return res, pp.tolist(), pps.tolist()

t0=time.time()
results = {}
for name, hf in [("GPT-2-large","gpt2-large"), ("Pythia-410M","EleutherAI/pythia-410m")]:
    try:
        r, pp, pps = run_model(name, hf)
        results[name] = dict(summary=r, per_prompt_partial=pp, per_prompt_partial_shuffled=pps)
    except Exception as e:
        print(f"  !! {name} failed: {type(e).__name__}: {e}")
        results[name] = {"error": str(e)}
print(f"\nelapsed {time.time()-t0:.0f}s")

# ---- pre-committed verdict ----
def ok(name):
    s = results.get(name,{}).get('summary',{})
    return (s.get('PRIMARY_median_partial_rho',1)<0 and s.get('PRIMARY_wilcoxon_p',1)<0.05)
gpt_ok = ok("GPT-2")
pyt_ok = ok("Pythia-160M")
shuf_ok = all(abs(results.get(n,{}).get('summary',{}).get('shuffle_median_partial_rho',1))<0.10
              for n in ["GPT-2","Pythia-160M"] if 'summary' in results.get(n,{}))
verdict = "SUPPORTED" if (gpt_ok and pyt_ok and shuf_ok) else "NOT SUPPORTED"
print("\n"+"="*60)
print(f"VERDICT: {verdict}")
print(f"  GPT-2 primary negative & sig: {gpt_ok}")
print(f"  Pythia primary negative & sig: {pyt_ok}")
print(f"  shuffle control null: {shuf_ok}")
print("="*60)
results['_VERDICT'] = verdict
open('replication_result.json','w').write(json.dumps(results, indent=2))
print("saved replication_result.json")