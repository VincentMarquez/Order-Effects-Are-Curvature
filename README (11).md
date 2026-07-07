# Try Consensus Curvature yourself

Everything in the paper (working draft v2.5) is runnable. Nothing requires trust.

## 60 seconds: test YOUR merge rule
```
python3 repro/try_your_merge.py        # demo table
```
```python
from try_your_merge import order_drift
drift = order_drift(my_fold)           # my_fold(state_or_None, item) -> state
# 0  => order-proof (flat).  >0 => your results depend on arrival order.
```
Also in there: `braid_defect(R)` — is your pairwise meeting protocol
order-of-meetings invariant? (Theorem D: only if someone keeps a verbatim copy.)

## Full check, no trust required
```
python3 repro/run_all.py               # Tiers 0-1: numpy/scipy only, ~2 min
python3 repro/run_all.py --full        # + transformer replication (torch, transformers 4.x PINNED)
```

## Claim -> script
| Claim | Script | Expected |
|---|---|---|
| Thm A (multitree = universal flatness) | `verify_consensus_curvature.py` | exhaustive census passes |
| Thm B/E (Stokes, constant exactly 1) | `repro/check_exact_math.py` C,D | ladder equality exact in Q; 0/300 violations |
| Thm C + Shapley identity | `repro/check_exact_math.py` E | core vs all 2^9 subsets; identity exact |
| Thm D (scribes; 1/8) | `repro/try_your_merge.py`, `exp2_scribe.py` | 1/8 to the digit; scribes exactly 0 |
| S8.2 drift table + design rule | `merge_drift_meter.py`, `repro/try_your_merge.py` | flat iff lossy step outside the fold |
| S8.3 replication (the -0.81 reversal) | `replicate_depth_controlled.py` + `audit_system_env.py` | NOT SUPPORTED; sign architecture-dependent |
| S8.5 rate law (Problem 10.4) | `repro/adoption_reverify.py` | log-log slope ~1.0, Spearman ~1.0 |
| Audit your own pipeline graph | `curvature_audit.py your_graph.json` | multitree = safe by shape |

## Environment
numpy>=1.24, scipy. Tier 2 only: torch + **transformers 4.x** (4.57 is the
environment of record; transformers 5.9 emits NaN rows in GPT-NeoX eager
attention — documented in the paper's S8 footnote).

## Provenance
AI-drafted (Claude, Anthropic) at the author's direction, 3 July 2026.
Pre-registered where it matters (`PREREG_depth_controlled.md`), adversarially
audited (`AUDIT_2026-07-03.md`), flagship claim falsified and reported (S8.3).
The git history is the lab notebook.
