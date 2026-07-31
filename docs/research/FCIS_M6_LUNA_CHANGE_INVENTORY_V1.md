# FCIS M6 Luna Change Inventory

Base: `babffa56dcbddc5886487fbb6e62740b15370000`  
Original implementation target: `84b344e3fac132047d83a61cf70ecd687c494161`
Original packet: `eba5f91e21b9bb901325382158de887135c4bec7`
Reviewed functional implementation target: `38c49c5be268a1c758e98f6b4b8ca131c1f054c6`
Exact-head delivery implementation target: `c5954655616629b657bb546207f11af518f897a8`
Exact-head delivery target tree: `e5a0c6040813570a811181a6d718234cdccb446b`

## Reviewed functional implementation target

Added or changed in the reviewed functional implementation commit:

- `.github/workflows/fcis-m6-durable-retraction.yml`
- `formal/esso/fcis_durable_retraction_v1.yaml`
- `src/core/fcis_durable_retraction.py`
- `tests/core/test_fcis_durable_retraction.py`

Inherited unchanged load-bearing files retained from the earlier implementation
and packet commits include the bounded Python/Julia models, frozen result,
Lean theorem, `lean-mathlib/lakefile.lean`, and hash-locked
`requirements-dev.lock.txt`. The functional commit is intentionally limited to
the listed implementation surfaces.

## Exact-head delivery implementation target

Added or changed in the exact-head delivery target:

- `.github/workflows/fcis-m6-durable-retraction.yml`

This target adds packet-only manifest/archive validation, deterministic archive
regeneration, post-commit delivery-receipt generation, and verified artifact
upload. It changes no functional core, runtime, datastore, authority,
migration, API, deployment, or value-moving path.

## Documentation-only packet child

The child adds the reviewed research documents, exact repair-input projection,
this inventory, the nonclaims, the source manifest, the exact toolchain record,
and one canonical archive. Its parent is the exact-head delivery target. It
changes no implementation or runtime authority path.

## Deletions

No files are deleted by the implementation target or packet child.

## Ignored/generated material excluded from both commits

Lean `.lake` outputs, Python caches, Ruff/mypy/Pytest caches, and the local
ESSO/mathlib dependency checkouts are verification material, not source
artifacts. Their exact commits are recorded where relevant in the repair report.
