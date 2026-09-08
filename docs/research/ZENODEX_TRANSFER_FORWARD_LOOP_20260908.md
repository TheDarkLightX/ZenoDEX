# Checked forward transfer loop

Date: 2026-09-08

Status: independently accepted finite-row algorithm correspondence with a
passing retained repository harness. `formal_core_complete=false`; authority `NONE`.

[AssetTransferForwardLoopV2.lean](../../lean-mathlib/Proofs/AssetTransferForwardLoopV2.lean)
relates an independently defined working-table algorithm to the existing
initial-balance scan and tail-first materializer. `checkedPut` reads the current
table, rejects a negative quantity before U128 overflow, then inserts or deletes.
`forwardRaw` processes owners from the head; `forward` sorts only after success.
No intermediate resource guard is introduced.

The central theorem covers both errors and exact final tables. Its premises
require unique positive account rows, initial canonical order and distinct
owners in the role list. `operationalCandidate_eq` derives the selected asset
binding and distinct roles from actual policy lookup and the V2 guards under
structural PRE admission. The computed forward candidate then feeds the same
final resource checks as the finite-outcome transition. It does not consume a
caller-supplied successful leaf or POST-admission witness.

Frozen source SHA-256:
`f90cf6c80f327f86b9542b0db93dad98cee8a3409b9a579c6120ea1bd349c53d`.

Root independently compiled the source under pinned Lean 4.27.0 after validating
26 dependency source/object hashes. Its consumer checks the exact central
contract, repeated-owner divergence and competing arithmetic failure order.
All 20 target theorem audits use standard Lean axioms.

Independent review compares 1,575 Python helper/Lean executions, including exact
returned rows and rejection codes. All 1,125 distinct-owner cases also match the
initial scan and tail result. It retains 60 duplicate-owner counterexamples,
four arithmetic endpoints and ten operational paths. The latter include an
intermediate 4,097-row table ending at an accepted 4,096 rows, and a final
4,098-row candidate rejected without effects. Four semantic false claims fail.

The retained
[forward-loop harness](../../tests/formal/test_lean_asset_transfer_forward_loop_v2.py)
checks all 20 theorem contracts and standard axioms, an independent admitted
state consumer, four false controls and the complete bounded comparison corpus
above. It builds the target as module 27 through the finite-outcome fixture and
uses four evaluator batches without dropping cases. The implementation agent's
focused replay passed four tests in 107.80 seconds. Root separately checked the
proof and consumer as described above and reviewed the retained harness. Ruff
lint and formatting checks passed.

```bash
python3 -m pytest -q tests/formal/test_lean_asset_transfer_forward_loop_v2.py
```

Retained harness SHA-256:
`7815500198229df1b9327f54fd32b670f57a11a6141e2c5772fdb660642cfc2b`.

The premises matter. Repeating an owner with initial balance one and delta minus
one causes the working loop's second update to reject, while scanning the initial
table twice misses the error. Reversing competing failing owners changes the
first failure. An empty working loop still sorts, so an unordered input cannot
be equated with the unchanged empty tail fold.

This proves a relation between two finite algorithms and supplies bounded tests
against the actual Python helper. Universal Python dictionary/parser and Rust
refinement remain open. The delta interface is a per-owner function; arbitrary
repeated owners with occurrence-dependent deltas are outside it. Production
preparation supplies distinct coalesced owners. Codec, compiler, cryptographic,
complete effect/journal, aggregate, replay and publication obligations remain
separate. No full Lake, Cargo, Kani, ESSO or guest proving was run for this
checkpoint. Concrete effect/journal construction and the combined asset-lane
gate remain integration obligations.
