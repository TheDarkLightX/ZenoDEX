# Constructed transfer effect-plan admission

This W09 increment extends `d25a6fa6c5f5731c9ec624e0276f373044512c72`.
It completes the six structural fields of the existing mathematical transfer
output using the selected pre-state policy and the actual sparse transition.
Runtime economics, wire formats and publication authority are unchanged.

## Contract

`AssetTransferEffectPlanV1.lean` constructs a plan from the existing
`AssetTransferPolicySelectionV1.step`. Accepted execution retains the actual
post-state and the canonical, aggregated account-movement and fee-allocation
rows from `AssetTransferSparseTablesV1.projectedPlan`. It adds:

- One asset-conservation row with derived pre/post account totals and supplies,
  and exactly zero authorized issue and burn.
- One fee-conservation row `(charged = allocations, residue = 0)` when the fee
  is positive; no fee-conservation row when the fee is zero.
- One ASSET_TRANSFER lane write and one occurrence consumption, carrying the
  explicitly supplied opaque commitment fields.
- An empty external outbox.

The construction preserves the underlying verdict and post-state. Rejection
retains the exact input state and an empty plan across all six fields.

The admission target starts from quantitative input constructor premises:

```text
StateAdmitted input.pre
=> EffectPlanAdmitted (complete commitmentFields input).plan
```

The initial premises bound the selected supply and account total, not merely
each individual row. Alias aggregation and zero-row elision precede canonical
sorting. There are at most three account-movement rows and one fee-allocation
row. The distinct effect kinds separate a fee annotation from a movement for
the same owner. Issue and burn projections are checked independently, so
inventing equal quantities of both cannot hide behind net-zero conservation.

This structural theorem needs no additional command-width premise. Command
constructor bounds and authenticated authorization remain separate obligations;
structural plan admission does not establish permission to move value.

The corresponding exact economic-table and supply-effect relations use the
post-state computed by the existing transition. They do not take a supplied
post-state, admitted plan or `Verified` result as evidence.

## Evidence and replay

The independent root replay recorded **7 passed in 53.39s**, with identical
semantic source hashes before and after execution. Ruff and single-file MyPy
passed. The harness rebuilds a fresh Std-only Lean 4.27 dependency closure,
restates all 18 public theorem signatures independently, and checks transitive
axioms against `propext`, `Classical.choice` and `Quot.sound`. The whole proof
also passed a separate direct compile with warnings treated as errors.

The nonempty witness constructs admitted initial accounts `40 + 5 = 45`, a
one-atom fee and a four-atom transfer. It applies both the admission theorem
and the exact table/supply relation theorem. The resulting balances are
`35/9/1`, with four economic rows, one asset row, one fee row, one lane write,
one occurrence and no outbox entry. Explicit arbitrary root strings in this
witness demonstrate the structural contract's lack of authentication.

Thirteen finite cases compare the public Python transition and the executable
Lean model across all six effect fields. They cover two assets, different fees,
fee-owner aliases, rejection precedence and signed-width neighbors. Movement
expectations are derived from submitted commands and policies; roots are
transported runtime observations. Rejections require exact codes, equal
pre/post roots, six empty effect fields and unchanged owned inputs.

The paired issuance/burn mutation first compiles as a well-typed constructor.
The witness proves its net projection still matches, while its separate issue
projection declares one atom against zero emitted atoms. The unchanged
`selectedPlan_projection` proof then fails on a complete private source copy.
The test checks the failure location and preserves the original source.

Two runtime controls retain the global boundary: positive sender fees fail the
fee-mirror check, and account-only conservation fails when physical custody
must also be counted. The latter declares 57 USD account atoms while the global
state owns 100 USD including custody; an accounts-only positive control passes.
The control first passes exact table/supply/lane-delta and fee-mirror checks,
isolating the conservation-state mismatch.

The long test functions keep complete Lean witnesses and their observations
together for review. They introduce no runtime complexity or algorithm change.

The proof SHA-256 is
`14cea53d90e1fdc6f068e581dcc8e737526475b323100c5d6c27b9354f769de9`.

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_effect_plan_v1.py
python3 -m ruff check \
  tests/formal/test_lean_asset_transfer_effect_plan_v1.py \
  experiments/v3_transfer_effect_plan_v1/render_evidence.py
python3 -m mypy tests/formal/test_lean_asset_transfer_effect_plan_v1.py
python3 -B -m experiments.v3_transfer_effect_plan_v1.render_evidence
```

The renderer declares source and test pins in
`THV1-20260906-transfer-effect-plan-v1.json`. Rendering executes no proof or
test and grants no authority.

## Remaining boundary

`EffectPlanAdmitted` checks the modeled row widths, signs, conservation,
separate projections, cardinalities and unique keys. It does not authenticate
the strings in the lane write or occurrence list. Those fields are explicit
inputs to this constructor. Copying actual runtime roots into a finite
comparison checks their transport; it does not prove hash construction,
canonical bytes, context provenance or current-store authority.

Global refinement imposes additional requirements. The V1 module's conservation
row measures account totals. `GlobalEconomicStateRefinementV2.ownedFor` and the
runtime global checker also count physical custody and reserves. Their
conservation-state relation requires its own conditions or the versioned
custody successor. Claimant liabilities are separate from physical assets.

A positive fee paid to the sender can pass the local transfer and structural
plan contracts. The global fee-mirror check still rejects it because the
sender's net movement is negative. This increment preserves that restriction;
it does not establish full `AnnotationMirrors` or change fee policy.

The global state carried by the sparse model retains its prior lane roots,
height and replay registry. The new output fields do not by themselves
construct `ExactLaneWrites`, `ExactReplayRefinement` or the full global
`Verified` relation. Historical profile admission, authentication, canonical
decoding, journals, cryptographic receipts, publisher mediation and recovery
remain separate obligations.

Finite executable comparisons do not establish universal Python, Rust or
compiler refinement. No full Lake/Mathlib, Cargo, guest, CUDA or release gate
is part of this increment. Other lane lifecycles and cross-lane composition
remain open. Formal-core completion and whole-program value safety remain
unestablished.
