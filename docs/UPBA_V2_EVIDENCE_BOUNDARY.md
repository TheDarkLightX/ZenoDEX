---
title: UPBA V2 Evidence Boundary
type: note
permalink: autonomous-tau-dex-review/docs/upba-v2-evidence-boundary
---

# UPBA V2 Evidence Boundary

This note records the evidence boundary for the UPBA v2 partial-fill verifier.

## Runtime Surface

The verifier is `src/core/uniform_batch_clearing.py`. V2 accepts certificates
only for this fixed policy:

```text
zenodex/upba_v2/fixed_admission_partial_fill_cpmm_exact_in
```

The certificate schema is:

```text
zenodex/uniform_batch_clearing_certificate/v2
```

The price objective remains:

```text
zenodex/upba_v1/net_flow_ratio_or_pool_spot_price
```

The objective id name remains v1 because the arithmetic objective is unchanged:
the canonical price is determined by aggregate executed net flow when both
directions are positive, otherwise by the reduced pre-pool spot ratio. V2
changes fill admissibility, not the price-objective formula.

## Runtime Checks

V2 keeps the v1 verifier checks and adds:

- schema and policy id must match exactly;
- each fill obeys `0 <= executed_in <= intent.amount_in`;
- zero fills must have `executed_out = 0`;
- zero fills are emitted as `FillAction.REJECT` with reason
  `UNIFORM_BATCH_UNFILLED`;
- at least one certificate fill must be positive;
- the canonical price objective uses executed net input, not full intent amount;
- v2 emits event type `UNIFORM_BATCH_CLEARING_V2`;
- certificate hash domain separation uses version `2`.

The accepted settlement is still compared against the supplied settlement at the
engine boundary when settlement matching is enabled.

## Formal Model

The aggregate execution model is
`lean-mathlib/Proofs/UniformBatchClearingV1.lean`.

The file now models `NetOrder` as executed net flow rather than full requested
flow. That makes the existing permutation and aggregate-sum theorems apply to
v2 after the runtime has validated `executed_in <= amount_in`.

Additional v2-relevant theorems:

- `reduce_price_ratio_positive`
- `canonical_price_objective_raw_positive`
- `canonical_price_objective_positive`

These prove that the model-side canonical price objective remains in the
positive-ratio domain when pool reserves are positive. This corresponds to the
runtime `_reduce_ratio` guard and prevents a zero denominator from entering
integer price arithmetic.

The starter optimality boundary is
`lean-mathlib/Proofs/UniformBatchOptimality.lean`. It proves:

- fixed-price aggregate volume upper bound:
  `matchedVolume <= min(acceptableDemand, acceptableSupply)`;
- fixed-price aggregate clearing feasibility;
- fixed-price aggregate clearing volume optimality;
- finite audit-set upper-bound certificates imply weak optimality inside the
  audited candidate list;
- runtime-strengthened audit certificates imply the winner is both present and
  weakly optimal inside the audited candidate list;
- audited-set optimality lifts to global weak optimality when the winner is
  feasible and the audited set is complete;
- audited-set optimality alone can omit a better candidate, so incompleteness is
  a formal non-claim rather than an implementation detail.

These optimality lemmas are model-level. They become runtime claims only after a
verifier binds acceptable side capacities or the audited candidate set to the
deployed solver path.

The current runtime verifier is exact over a finite audited set. It is an
approximation to global optimality whenever that audited set is a sample,
heuristic frontier, or otherwise incomplete. It becomes a proof of global weak
optimality only when a separate completeness argument establishes that every
feasible candidate is in the audited set.

The first runtime bridge for the finite audited-set theorem is
`src/core/uniform_batch_optimality.py`, documented in
`docs/UPBA_OPTIMALITY_CERTIFICATE.md`. It verifies that a declared winner is
weakly optimal inside a certificate-supplied audited candidate set. This still
does not prove the audited set is complete.

The checker also exposes a bound verification path that derives the winner
candidate id from the UPBA certificate hash. This prevents a valid audited-set
optimality certificate from being replayed as evidence for a different UPBA
settlement certificate.

The DEX engine now wires this bound verifier into the optional settlement
envelope field `uniform_batch_optimality_certificate`. When supplied, the
certificate must bind to the attached `uniform_batch_certificate`; otherwise
settlement fails closed before state application.

## Tests

Focused runtime checks:

```bash
pytest -q tests/core/test_uniform_batch_clearing.py \
  tests/core/test_uniform_batch_optimality.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py
```

Nearby integration checks:

```bash
pytest -q tests/integration/test_dex_engine.py \
  tests/core/test_uniform_batch_clearing.py \
  tests/core/test_uniform_batch_optimality.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py \
  tests/core/test_settlement_strong_validator.py \
  tests/core/test_batch_greedy.py
```

Focused Lean check:

```bash
cd lean-mathlib
~/.elan/bin/lean Proofs/UniformBatchClearingV1.lean
~/.elan/bin/lean Proofs/UniformBatchOptimality.lean
```

## Aristotle Optimality Lane

UPBA v2 is a verifier bridge. It checks a proposed certificate against the fixed
admitted set. The starter Lean optimality lemmas above do not yet prove that the
solver found the globally optimal admitted set, price, or welfare objective.

An Aristotle proof-search packet was submitted and returned for the next
optimality layer:

```text
abee69ad-e2a3-47ce-8c0f-71491635f5d3
```

The packet asks for two scoped theorem families:

- fixed-price aggregate volume optimality:
  `matchedVolume <= min(acceptableDemand, acceptableSupply)`;
- finite audit-set certificate optimality:
  a verifier-checked upper-bound certificate implies weak optimality by volume
  first and surplus second inside the audited candidate list.

The local starter proof covers those theorem shapes, and Aristotle independently
proved the same submitted theorem statements. The receipt is
`lean-mathlib/proof_receipts/upba_v2_aristotle_optimality.md`.

The next stronger theorem should bridge per-order admissibility to aggregate side
capacities, then bind that bridge to a runtime-auditable candidate-set
certificate.

## Current Non-Claims

UPBA v2 does not currently claim:

- volume-maximizing or surplus-maximizing clearing across all prices;
- fair order inclusion;
- censorship resistance;
- oracle-safe mark price construction;
- exact-out support;
- multi-hop support;
- LP add/remove support inside the uniform batch;
- full MEV elimination.

The current claim is narrower: for the scoped single-pool exact-in surface, a
v2 certificate can express partial fills and explicit unfilled members while
remaining bound to deterministic aggregate-flow arithmetic and aggregate CPMM
invariant checks.
