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

## Finite effect-plan construction

[AssetTransferFiniteEffectPlanV2.lean](../../lean-mathlib/Proofs/AssetTransferFiniteEffectPlanV2.lean)
constructs the existing six-field effect plan from the finite transition's actual
selected policy and computed POST. It proves numeric plan admission, canonical
ordering and key uniqueness, token validity under command admission, and an
eight-item ceiling. Rejection produces the existing empty plan.

The ownership relation is stronger than total conservation: for every owner
and asset, the account movement equals that account's actual POST minus PRE.
The fee allocation names exactly the selected collector, asset and account
domain. Other effect kinds, assets and domains receive zero. Aliasing the
collector with the sender or recipient preserves the coalesced account delta;
the fee allocation does not become a second physical movement. Accepted plans
also bind the conservation fields, lane roots and occurrence identifier to
their computed sources, with an empty outbox.

Proof SHA-256:
`ff36e13be89431ac338b8df685336584fde6fba929808001a130fba1de49f6d6`.
Retained harness SHA-256:
`952fefcff8c435a0508e749ea4473aa27e6e93e4987d29e90176871fdb149904`.

Root reviewed and independently compiled the frozen proof with pinned Lean
4.27.0 and verified dependency source/object hashes. The independent author
consumer and axiom audit replayed successfully: 50 target/consumer declarations
used only standard axioms. Four false controls failed with the intended false
proposition, covering a zero-fee row, wrong collector, wrong debit and wrong
field root. The retained harness separately checks the declaration/signature
surface, a nonvacuous consumer, an axiom-parser negative control and raw-row
alias/fee false controls.

The retained Python/Lean comparison observes all six concrete plan fields for
six accepted cases: zero fee, distinct collector, both collector aliases,
maximum-length escaped identifiers and the exact I128 minimum debit. It checks
exact PRE/POST bytes for these cases and supplies their actual runtime roots
through a finite digest lookup. A seventh case exceeds the 4,096-row cap with
two new credits and checks typed rejection, unchanged state, six empty plan
fields and labelled zero effect queries. The large case uses compact Lean
evaluation and byte-length observations. This is bounded implementation evidence.

Independent root replay:

```bash
python3 -m pytest -q tests/formal/test_lean_asset_transfer_finite_effect_plan_v2.py
python3 -m ruff check tests/formal/test_lean_asset_transfer_finite_effect_plan_v2.py
python3 -m ruff format --check tests/formal/test_lean_asset_transfer_finite_effect_plan_v2.py
git diff --check
```

All five tests passed in 103.69 seconds; lint, formatting and diff checks passed.
The first replay exposed harness elaboration and expected-query mistakes. The
repairs retain the intended semantic false checks and explicitly observe zero
queries on rejection; they change no economic rule or runtime implementation.
The V3 plan checker passes. The broader claims-registry check still fails at
`claims[123]` because `tools/check_derivatives_authorization_matrix.py` is missing;
this existing failure is not suppressed by the scoped proof checks.

This construction reuses the existing plan carrier and source-only test
fixtures. No new plan abstraction or proof-build framework was added. Its exit
condition is the checked construction and per-owner relation; universal codec,
journal and authentication refinement remains separate work.

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

The finite plan now represents all six concrete effect fields. Their complete
wire encoding and journal correspondence remain unproved. An independent
4,787-byte upper estimate under runtime token, numeric and canonical-root bounds
does not prove concrete constructor admission; the eight-item bound is proved
separately. Inspection of the Python/Rust constructors and replay of small Python
constructor cases found no additional failure under the reviewed typed-input
assumptions. That review is not a universal constructor theorem or Rust replay.
Owned chain, deployment, profile, epoch and occurrence fields, command-body
hashing, complete effect/journal encoding, dictionary/parser correspondence,
aggregate resources, replay and publication remain separate obligations.

No full Lake, Kani, ESSO, Rust execution, guest proving, release promotion or live
activation is claimed by this checkpoint. Concrete effect/journal constructor
correspondence remains an integration obligation. The separately retained
combined asset-lane gate covers its finite outcome registry; it does not close
these representation and authority obligations.
