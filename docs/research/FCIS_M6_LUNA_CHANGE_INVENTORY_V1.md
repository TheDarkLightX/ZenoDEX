# FCIS M6 Luna Change Inventory

Base: `babffa56dcbddc5886487fbb6e62740b15370000`  
Original implementation target: `84b344e3fac132047d83a61cf70ecd687c494161`
Original packet: `eba5f91e21b9bb901325382158de887135c4bec7`
Prior packet head: `7deeb3403c933402393d15553cc87563aa71b752`
Reviewed functional implementation target: `ecf26f987c3d6393501fec66ddfc3429fb8634c7`
Reviewed functional implementation tree: `fdf154ac143a9f9a9e840fbbf49761190d138920`

## Reviewed functional implementation target

Added or changed in the current reviewed functional implementation commit:

- `.github/workflows/fcis-m6-durable-retraction.yml`
- `src/core/fcis_durable_retraction.py`
- `tests/core/test_fcis_durable_retraction.py`
- `tools/check_fcis_durable_retraction_model.py`

The commit binds sequence into publication identity, closes retry sequence and
authority-epoch admission, removes importable authority-minting tokens and
built-in accepting verifiers, requires fresh shell-selected verifier decisions
at authority-bearing uses, and replaces mandatory private ESSO checkout with a
self-contained exhaustive checker for the public finite-state model.

Inherited unchanged load-bearing files include the bounded Python/Julia models,
frozen result, ESSO-IR source, Lean theorem, `lean-mathlib/lakefile.lean`, and
hash-locked `requirements-dev.lock.txt`.

## Documentation-only packet child

The child adds the reviewed research documents, exact repair-input projection,
this inventory, the nonclaims, the source manifest, the exact toolchain record,
the Luna continuation prompt, and one canonical archive. Its parent is the
reviewed functional implementation target. It
changes no implementation or runtime authority path.

## Deletions

No files are deleted by the implementation target or packet child.

## Ignored/generated material excluded from both commits

Lean `.lake` outputs, Python caches, Ruff/mypy/Pytest caches, and the local
Private ESSO and mathlib dependency checkouts are verification material, not
source artifacts. Their exact commits are recorded where relevant in the repair
report.
