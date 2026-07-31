# FCIS M6 Luna Change Inventory

Base: `babffa56dcbddc5886487fbb6e62740b15370000`  
Implementation target: `84b344e3fac132047d83a61cf70ecd687c494161`

## Implementation target commit

Added or changed:

- `.github/workflows/fcis-m6-durable-retraction.yml`
- `experiments/fcis_durable_retraction_bounded_search.py`
- `experiments/fcis_durable_retraction_bounded_search_result.json`
- `experiments/julia/fcis_durable_retraction_oracle.jl`
- `formal/esso/fcis_durable_retraction_v1.yaml`
- `lean-mathlib/Proofs/FCISDurableRetraction.lean`
- `lean-mathlib/lakefile.lean`
- `src/core/fcis_durable_retraction.py`
- `tests/core/test_fcis_durable_retraction.py`

## Documentation-only packet child

The child adds the reviewed research documents, exact repair-input projection,
this inventory, the nonclaims, the source manifest, and one canonical archive.
It changes no implementation or runtime authority path.

## Deletions

No files are deleted by the implementation target or packet child.

## Ignored/generated material excluded from both commits

Lean `.lake` outputs, Python caches, Ruff/mypy/Pytest caches, and the local
ESSO/mathlib dependency checkouts are verification material, not source
artifacts. Their exact commits are recorded where relevant in the repair report.
