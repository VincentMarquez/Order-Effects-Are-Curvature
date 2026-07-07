# Project Structure

```
Order-Effects-Are-Curvature/
│
├── lean/                          # Lean theorem prover proofs
│   ├── CurvatureCalculus.lean    # Curvature calculus definitions and theorems
│   └── RateLaw.lean              # Rate law formalization
│
├── python/                        # Python implementation and analysis
│   ├── src/                       # Main package source code
│   │   └── __init__.py
│   │
│   ├── scripts/                   # Executable analysis scripts
│   │   ├── adoption_reverify.py
│   │   ├── audit_system_env.py
│   │   ├── check_exact_math.py
│   │   ├── check_rate_law.py
│   │   ├── curvature_audit.py
│   │   ├── explore_open_residuals.py
│   │   ├── replicate_depth_controlled.py
│   │   ├── replicate_scale.py
│   │   ├── run_all.py            # Master script to run all analyses
│   │   └── try_your_merge.py
│   │
│   ├── data/                      # Data files and results
│   │   └── explore_open_residuals.json
│   │
│   └── logs/                      # Log files from runs
│       └── (generated at runtime)
│
├── README.md                      # Project overview
├── requirements.txt               # Python dependencies
├── .gitignore                     # Git ignore rules
└── LICENSE                        # MIT License
```

## Directory Guide

- **lean/**: Formal proofs and definitions in Lean 4
- **python/src/**: Core Python modules and utilities
- **python/scripts/**: Standalone analysis and verification scripts
- **python/data/**: Input and output data files
- **python/logs/**: Log files from script executions
