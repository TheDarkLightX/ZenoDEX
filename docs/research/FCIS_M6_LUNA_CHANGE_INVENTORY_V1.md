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

## Receipt-rebind repair child (2026-08-03)

The receipt-rebind implementation target is commit
`91bce42607c2c2365087976bed1bee4a38cc1812`, tree
`d79465f3abc421838d6864368a57ac2ef48dc3ca`, with prior packet head
`f36e1e301135b69a39f040e34c7de79a40054ff8` as its parent. Its two changed
files are the fail-closed task-packet validator and its permanent regression
test. The following child contains receipt, manifest, report, and public-text
updates only. It has no functional-core, runtime, datastore, authority,
migration, deployment, or value-moving changes.

## Dependency-assurance rebind child (2026-08-04)

The dependency-assurance implementation target is commit
`2c3f21d87d49a31bceb1e74b19077bebcdb3cd2c`, tree
`16e6a2ee03e9e949431605c493c7ff9bc3aad5c7`, with prior packet head
`3c2a016e7ae702bddcca47831e15a5d17509010f` as its parent. It raises the
minimum fixed Python cryptography and MCP versions, refreshes the hash-locked
Python environments, removes audited UI transitive vulnerabilities, and moves
the four affected RISC0 locks to patched `ruint` and non-yanked `spin`
releases. The generated dependency ratchet and FCIS support-root source
manifest are rebound to the exact implementation tree.

The following child updates only this packet's report, toolchain identity,
manifest, integrity ledger, and canonical archive. It changes no functional
core, runtime transition, datastore, authority, migration, deployment, or
value-moving path.

## Sealed-evidence compatibility repair child (2026-08-04)

The sealed-evidence compatibility implementation target is commit
`9bc1a0f2bc271021432f690f3628e8cf58aa6996`, tree
`7e493180bf0c17185d71a926d4a6952e8ce955c2`, with prior packet head
`4ff2122ebcc5ea848361dad23d7d587c304cac10` as its parent.

The target restores the four RISC0 lockfiles to their retained proof-source
identities after the patched dependency graph produced different guest image
identities. It records `RUSTSEC-2026-0220` as narrowly dispositioned residual
debt for the unmounted proof lanes, binds that disposition to exact
`risc0-binfmt 3.0.4` source observations, and requires fresh image IDs,
receipts, and source-bound replay evidence before removal.

The target also repairs the B1B compatibility workflow. Event diffs are
derived from the trusted pull-request merge base and filtered through the
closed B1B ownership surface. The sealed historical B1B packet remains
byte-identical and ancestry-checked. The later state-binding research chain is
explicitly closed, while any consumer outside that exact unmounted chain is a
reachability failure.

The following child updates this packet's report, toolchain identity,
manifest, integrity ledger, and canonical archive. It changes no functional
core, runtime transition, datastore, production authority, migration,
deployment, or value-moving path.
