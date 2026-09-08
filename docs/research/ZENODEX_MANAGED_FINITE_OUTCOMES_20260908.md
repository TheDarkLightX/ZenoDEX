# Finite managed-asset outcomes

Date: 2026-09-08

Status: the frozen theorem source compiles and has independent scoped review
acceptance. The retained focused harness passes independent replay.
`formal_core_complete=false`;
authority remains `NONE`.

## Contract

[ManagedAssetFiniteOutcomeV2.lean](../../lean-mathlib/Proofs/ManagedAssetFiniteOutcomeV2.lean)
owns the complete managed leaf: release, ordered policies, account rows and
complete supply rows. Policy lookup, selected balances, supply and account totals
come from these tables. The policy and state encoders include the actual owned
metadata fields, extending the
[byte-accounting relation](ZENODEX_ASSET_LANE_BYTE_ACCOUNTING_20260908.md).

The transition preserves the five context checks before policy lookup. It then
uses the existing selected-policy economic guards, computes the full candidate
tables and checks their resource limits. The old 21-code economic prefix remains
unchanged; the finite model has 22 codes including `STATE_RESOURCE_LIMIT`.

```text
accepted iff economic guards pass and Resources(computed candidate)
resource rejection iff economic guards pass and not Resources(computed candidate)
any rejection implies exact original state and empty effects
```

`economic_candidate_structural` derives candidate structure from admitted PRE
tables and successful economic guards. Its premises include unique ordered
keys, identical ordered policy/supply asset lists, nonzero supported U128 account
rows, U128 supplies, accounts custody and account totals at most supply.
It does not require an independently supplied successful leaf or POST admission.

`candidate_resources_iff_source_capacity` relates the actual candidate limits
to source-derived row and byte costs. `accepted_accounting` preserves unrelated
assets and applies the selected signed change to accounts and supply.
`accepted_supply_identity` retains complete supply identities through a full
burn. `trace_prefixes_admitted` preserves admitted state through lists of actual
accepted and rejected transitions under explicit command admission assumptions.

## Evidence

Frozen source SHA-256:
`7b9f48708aac9ecc491c06af78cdc1d4d8ea7c0d60ec2353c91ee7a010168a9b`.
Root independently compiled it under pinned Lean 4.27.0 with warnings as errors,
after rechecking the source/object hashes of the previously fresh-built
24-module dependency chain. Its owned encoders matched 72 exact byte arrays
from 36 admitted Python policy/state pairs. Cases include optional authorities,
all asset classes and maximally escaped 160-byte subjects.

Independent review compiled the target and its own consumers, audited standard
axioms, and checked 29 typed Python/Lean cases. Twenty compare whole POST bytes;
larger cases compare rows, supply identities, amounts, byte counts and rejection
no-op observations. These include actual byte-cap neighbors, row capacity,
signed-width boundaries and earlier economic failures. The review also checked
the exact ordered 22-code Lean/Python/Rust registry and five negative controls.
Rust source inspection here is distinct from Rust execution.

The retained [finite outcome harness](../../tests/formal/test_lean_managed_asset_finite_outcome_v2.py)
checks all 42 theorem declarations, ten exact public signatures, standard axioms,
a finite issue/reject/full-burn/reissue trace, symbolic row-cap rejection and
four semantic negative controls. It also evaluates actual finite policy, balance,
supply, context and command values for 37 runtime cases, comparing each verdict
and complete POST-state byte sequence with Python. The negative controls reject
omitting the resource code, changing context/policy failure priority, consuming
an occurrence on rejection and deriving state equality from a constant digest.

Initial independent root replay:

```bash
python3 -m pytest -q tests/formal/test_lean_managed_asset_finite_outcome_v2.py
# 4 passed in 92.47s
python3 -m ruff check tests/formal/test_lean_managed_asset_finite_outcome_v2.py
# All checks passed!
```

Initial harness SHA-256:
`729e894630c05584de4201e358c08a3e367d596f3b26a38f9f79d1631f353ef7`.
The retained replay builds the 25-module source closure in its isolated fixture.
The subsequent retained
[resource harness](../../tests/formal/test_lean_managed_asset_finite_resource_v2.py)
evaluates compact actual finite tables at both byte-cap neighbors and the
4,096-row dormant-owner boundary. It checks every source row against the compact
recipe, verifies shared command/context identity, and compares economic verdict,
computed candidate admission, PRE/candidate/POST byte counts, table counts,
supply and account totals, exact model rejection no-op and effect counts.
Python separately compares the full expected boundary POST bytes.

The first oracle implementation omitted the supply increment when adding a new
owner. Equal decimal widths concealed the error from byte-length comparisons.
The corrected oracle increments both balance and supply, observes candidate
supply values and retains a one-atom same-width regression. This was a test
oracle defect; no production transition defect is inferred.

```bash
python3 -m pytest -q tests/formal/test_lean_managed_asset_finite_resource_v2.py
# Independent root replay: 2 passed in 79.55s
python3 -m ruff check tests/formal/test_lean_managed_asset_finite_resource_v2.py
# All checks passed!
```

Initial resource harness SHA-256:
`ec292ea6075843bccf12bb5f31d7f25bb8cf16cf3ee0979bf700eb82400ebf1a`.
These three computed boundary observations extend the retained corpus.

The scalar parity report now explicitly checks its fixed 21-code economic
prefix. The finite harness evaluates the complete 22-code Lean registry and
compares its order and ranks with the unfiltered runtime enum. Full reachable
runtime coverage adds the actual dormant-owner resource rejection, requiring
unchanged roots and empty effects. All 37 original twins, ten acceptances,
eight history steps and M1/M2/M3 controls remain. Only the two existing
constructor-unreachable codes remain exempt from runtime coverage.

The implementation agent's combined run of the scalar parity, finite outcome
and finite resource harnesses passed 180 tests in 297.45 seconds. The migrated
scalar and finite harness hashes are respectively
`14f54146edc5152cb57796a01dad1ba9ffb5b04555e25a6e311454fa8f245b0b`
and `046df765c6752612961c1eae5c82bd7949a8b165255c92cae6813b889e0c4ef2`.

The resource oracle was then simplified to one issue-one-atom operation. It
derives balance and supply increments from PRE instead of carrying two selector
modes, two supply updates and hard-coded candidate amounts. All three retained
candidate byte sequences are identical to the prior oracle, and the one-atom
regression remains. This removes duplicated test accounting; it changes no
production transition or formal statement. Its source hash is
`8d4c4fbe89f92e441b760849a17667023630e59d5e900d152112bcc6706d79c5`.
Root replay then passed both resource tests, the full runtime coverage test and
the finite enum/rank test, alongside the transfer finite-vector test: five
tests passed in 322.54 seconds. Ruff lint and formatting checks passed for the
changed finite harnesses; the older scalar file retained its existing formatting.
Universal runtime refinement remains open.

The claims-registry check still fails on the existing missing
`tools/check_derivatives_authorization_matrix.py` evidence file.

## Finite managed effect-plan construction

[AssetLaneFiniteEffectPlanV2.lean](../../lean-mathlib/Proofs/AssetLaneFiniteEffectPlanV2.lean)
now constructs the six-field `GlobalSettlementCoreV2.EffectPlan` from the actual
finite outcome. For accepted issue and burn commands, its 17 theorems establish
signed row bounds, unsigned conservation quantities, issue/burn and fee
projections, unique ordered keys, item limits and valid tokens. The plan binds
the actual finite PRE/POST root observations and accepted occurrence; rejection
returns six empty fields. Candidate structure is derived from admitted PRE and
successful guards. No caller-supplied POST admission is assumed.

The [retained harness](../../tests/formal/test_lean_asset_lane_finite_effect_plan_v2.py)
compiles the source closure, checks all declarations and standard axioms, and
checks six public theorem signatures. Its independent consumer issues from zero
supply and fully burns the result. Bounded observations of all six plan fields
agree with the actual Python constructors. Two semantic false controls reject
reversed burn signs and omission of the supply-effect row.

```bash
python3 -m pytest -q tests/formal/test_lean_asset_lane_finite_effect_plan_v2.py
# Independent root replay: 4 passed in 65.82s
```

Proof SHA-256:
`24ac1efe7c06732d3c4d7dd37269d2b6afb64bb8d18a7b4893f9460b47b82fc3`.
Harness SHA-256:
`0e4139b07348d3905a78b7ab0abcbac043978862574161ea535391c83d57b5d6`.
Independent mathematical review also compiled its own consumers and checked
typed Python issue/full-burn observations. These are scoped construction and
bounded parity results, not universal implementation refinement.

The retained constant-digest example deliberately demonstrates the boundary:
numeric plan admission can hold while Python rejects the resulting root syntax.
The subsequent [exact effect-plan encoder and byte-bound proof](ZENODEX_TRANSFER_FINITE_OUTCOMES_20260908.md#exact-effect-plan-encoding-and-derived-byte-bound)
adds explicit canonical-root and nonzero-occurrence syntax premises, encodes the
six-field plan plus schema, and derives an 8,192-byte bound for actual accepted
managed plans. It also proves the exact empty rejection encoding. These syntax
premises authenticate nothing. Journal admission, authentication and universal
Python/Rust correspondence remain open.

## Remaining refinement

Root and namespace syntax are explicit external predicates on immutable
metadata. The state-root observer is an arbitrary function of encoded bytes;
it supplies no collision resistance, valid-root encoding or authentication.
Command-body hashes and occurrence identities are supplied observations in
this model, whereas the implementations derive them cryptographically.

Universal Python/Rust serializer, lookup/sort and constructor correspondence
remains open. The finite numeric plan and explicit encoder theorems do not
establish all actual effect-plan or journal validators. The derived model byte
bound supersedes the earlier informal 2,700-byte estimate as checked evidence;
it is not a validator-refinement theorem. The five-item bound remains separate.

Typed PRE-constructor failures, global replay protection, accumulated effect
admission, coordinator resources, authenticated snapshots, publication and
recovery remain separate obligations. No full Lake, Kani, ESSO, RISC0 proving
or production promotion was performed for this checkpoint. The subsequent
encoding review built the small Rust ABI library and replayed ten complete
plan byte arrays through its typed decoder/re-encoder, with seven negative wire
controls; it did not execute Rust transitions or the full Cargo test suites.
