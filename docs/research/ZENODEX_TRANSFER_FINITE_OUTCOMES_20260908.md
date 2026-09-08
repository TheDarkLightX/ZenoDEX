# Finite transfer outcomes

Date: 2026-09-08

Status: frozen source independently checked and accepted for its finite-state
contract, with retained repository replay. Authority remains `NONE`;
`formal_core_complete=false`.

## Contract

[AssetTransferFiniteOutcomeV2.lean](../../lean-mathlib/Proofs/AssetTransferFiniteOutcomeV2.lean)
owns the release, policies, balances and complete supply table. Policy lookup
and selected arithmetic observations come from those tables. Policy and state
encoding uses the owned fields. Acceptance requires successful economic guards
and resource admission of the actual computed candidate.

The first five context guards precede policy absence. The existing ordered
forward owner scan determines arithmetic failure. The materialized final table
receives the row and byte checks; intermediate table size cannot reject a
candidate that fits. The finite rejection registry retains the economic prefix
and adds `STATE_RESOURCE_LIMIT`, for 18 total codes.

Structural admission requires unique canonical keys, supported positive U128
account rows, complete U128 supplies, matching ordered policy/supply keys and
per-asset account totals at most supply. Strict supply slack is permitted.
Economic success derives candidate structure without assuming POST admission.
Acceptance preserves admission and every asset's account total; complete
supplies, policies and release remain unchanged. Rejection returns exact PRE
and empty effects. Trace theorems preserve admission at every prefix, under
explicit command admission assumptions.

## Qualification evidence

Source SHA-256:
`97eaaa3f7e7ec8859d6a28b7fc6de49586f8d7ce983f70908144dd92beb1f09c`.

Root independently compiled this source using pinned Lean 4.27.0 and 25
source/object-verified dependencies. Its separate audit checked all 42 theorem
declarations for standard axioms and absence of trust placeholders. Root also
replayed the author's consumer, including exact two-credit successor rows,
alias coalescing, forward rejection priority, and symbolic resource boundaries.

Independent review assembled 37 typed Python/Lean cases, exercised all 18
rejection codes and compared 31 complete POST-state byte sequences. Accepted
movement and fee rows also agree. Resource observations include a two-credit
row overflow, a transient extra row followed by sender deletion, and actual
1,048,576-byte acceptance / 1,048,577-byte rejection. The review's independent
consumer proves inhabited admission with strict account cover and a mixed
accepted/rejected trace. Five semantic false claims fail at their intended gates.

The author's separate serializer campaign compares 192 exact byte arrays across
96 admitted Python policy/state pairs. Both campaigns are bounded evidence.
The ordered Python/Rust rejection registries were inspected; the review did not
execute Rust. The retained
[finite-outcome harness](../../tests/formal/test_lean_asset_transfer_finite_outcome_v2.py)
checks the theorem surface, independent admission/trace consumer, five semantic
false controls and all 37 typed runtime vectors. Root's three proof checks passed;
the single large vector invocation exceeded its compiler timeout. The harness
now evaluates the same 37 vectors in batches of four and checks the exact
registry, order and complete combined results. No cases or checks were removed.
Root replay of that changed test passed alongside four managed finite checks:
five tests passed in 322.54 seconds. All other test bodies remain unchanged.
Ruff lint and formatting checks passed.

Retained harness SHA-256:
`8aef8c119b152b35545f89dee87b940b7d465a2b3442eea5be252adca2c1f27b`.
No old gate or source pin has been weakened.

## Remaining refinement

The finite arithmetic materializer folds owner updates from the tail. The
[checked-forward-loop relation](ZENODEX_TRANSFER_FORWARD_LOOP_20260908.md)
proves equality with the operational put/delete order and final sort under its
unique-row, positive-row, canonical-order and distinct-owner premises. The
economic failure scan retains its forward order. Universal implementation
refinement still requires the concrete representation and constructor relations.

Root syntax and namespace checks remain explicit external predicates. The digest
observer is arbitrary. An admitted model can accept with a constant string
digest that the actual runtime lane-write constructor rejects. Therefore valid
root encoding and cryptographic correspondence must be established before
claiming runtime constructor equivalence.

The abstract effects omit parts of the concrete effect schema and journals.
An independent 4,787-byte/eight-item upper estimate under runtime token,
numeric and canonical-root bounds does not prove concrete constructor admission.
Owned chain, deployment, profile, epoch and occurrence fields, command-body
hashing, complete effect/journal encoding, dictionary/parser correspondence,
aggregate resources, replay and publication remain separate obligations.

No full Lake, Kani, ESSO, guest proving, release promotion or live activation is
claimed by this checkpoint. Concrete effect/journal constructor correspondence
and the combined asset-lane gate remain integration obligations.
