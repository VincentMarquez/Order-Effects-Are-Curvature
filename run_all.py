#!/usr/bin/env python3
"""One command, whole framework. Usage:
   python3 run_all.py            # Tiers 0-1 (numpy/scipy only), ~2 min
   python3 run_all.py --full     # + Tier 2 transformer replication (torch + transformers 4.x)
"""
import subprocess, sys, pathlib, importlib
HERE=pathlib.Path(__file__).resolve().parent; CC=HERE.parent
TIERS=[("Tier0 exact math (Thms A-E, rationals)", HERE/"check_exact_math.py"),
       ("Tier0 rate law (Thm 5.x, numeric+exact)", HERE/"check_rate_law.py"),
       ("Tier0 open residuals (identity/lifts/Z-bound)", HERE/"explore_open_residuals.py"),
       ("Tier1 your-merge instruments (Prop 3.4 + Thm D)", HERE/"try_your_merge.py"),
       ("Tier1 S8.5 reverify (Perron rate + placement)", HERE/"adoption_reverify.py"),
       ("Tier1 scribe/braid experiment", CC/"exp2_scribe.py"),
       ("Tier1 fusion Stokes localization", CC/"exp4_fusion.py"),
       ("Tier1 robust-core instrument", CC/"exp6_robustcore.py"),
       ("Tier1 37-check verification suite", CC/"verify_consensus_curvature.py")]
if "--full" in sys.argv:
    try:
        import transformers
        if int(transformers.__version__.split(".")[0])>=5:
            print("WARNING: transformers>=5 emits NaN GPT-NeoX attention (see paper footnote); pin 4.x")
        TIERS.append(("Tier2 depth-controlled transformer replication", CC/"replicate_depth_controlled.py"))
    except ImportError:
        print("(--full requested but torch/transformers missing; skipping Tier2)")
board=[]
for name,path in TIERS:
    if not path.exists(): board.append((name,"MISSING")); continue
    r=subprocess.run([sys.executable,str(path)],capture_output=True,text=True,cwd=CC,timeout=3600)
    tail=[l for l in r.stdout.strip().split("\n") if l][-1] if r.stdout.strip() else ""
    board.append((name, "OK" if r.returncode==0 else "FAIL", tail[:70]))
print("\n"+"="*74+"\nSCOREBOARD\n"+"="*74)
for row in board: print("  {:52s} {}".format(row[0], " | ".join(row[1:])))
fails=[b for b in board if b[1] not in ("OK",)]
print("="*74)
print("ALL GREEN" if not fails else f"{len(fails)} item(s) not OK")
sys.exit(0 if not fails else 1)
