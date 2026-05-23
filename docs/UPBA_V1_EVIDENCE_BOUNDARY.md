---
title: UPBA V1 Evidence Boundary
type: note
permalink: autonomous-tau-dex-review/docs/upba-v1-evidence-boundary
---

# UPBA V1 Evidence Boundary

This note records the current evidence boundary for the UPBA v1 production
candidate path.

## Runtime Surface

The verifier is `src/core/uniform_batch_clearing.py`. It accepts a certificate
only for this fixed policy:

```text
zenodex/upba_v1/fixed_admission_full_fill_cpmm_exact_in
```

The price objective is fixed to:

```text
zenodex/upba_v1/net_flow_ratio_or_pool_spot_price
```

The accepted surface is deliberately narrow: one active CPMM pool, exact-in
swaps only, full fills only, one certificate fill per admitted intent, one
canonical reduced rational price, and one aggregate reserve update.

## Formal Model

The Lean model is `lean-mathlib/Proofs/UniformBatchClearingV1.lean`.

It proves:

- `uniform_execution_permutation_invariant`
- `uniform_execution_is_linear_aggregation`
- `uniform_execution_append_decomposes`
- `canonical_price_objective_raw_eq_of_equal_net_sums`
- `canonical_price_objective_eq_of_equal_net_sums`
- `canonical_price_objective_raw_permutation_invariant`
- `canonical_price_objective_permutation_invariant`
- `canonical_price_objective_permutation_invariant_via_net_sums`

The model captures the algebraic fact UPBA v1 relies on:

```text
same admitted multiset -> same aggregate deltas and same canonical price target
```

The aggregate-sum theorems are the closest formal boundary to the runtime
verifier: once fee-adjusted net base and quote input are fixed, the canonical
price objective is fixed. Permutation invariance follows as a corollary because
permutation preserves those sums.

The theorem is intentionally about a fixed admission set. It does not prove that
the admission set is fair, inclusion-resistant, or welfare-optimal.

## Runtime Checks

The Python verifier binds the Lean model boundary to runtime by requiring:

- closed certificate and fill schemas;
- the expected policy id;
- the expected price objective id;
- bounded price, output, fill count, and admission count domains;
- a committed pre-pool snapshot hash;
- a committed fixed intent-set hash;
- sorted canonical fills;
- exactly one fill per admitted intent;
- full intent input consumption;
- cross-multiplied limit-price checks;
- canonical reduced price objective;
- aggregate CPMM invariant preservation;
- settlement equality at the engine boundary.

## Grid Economic Profile

The bounded-grid theorem is exact over the configured finite grid. Economic
sufficiency of a grid resolution is a separate deployment profile.

`tools/upba_v1_grid_economic_profile.py` evaluates built-in candidate profiles
with this conservative bound:

```text
epsilon_price = 1 / (2D)
abs_error(p, D) <= epsilon_price
relative_error_bps <= ceil(10_000 / (2D * p_min))
output_error_units <= ceil(max_gross_input_per_fill / (2D)) + 1
```

The first built-in profiles are documented in
`docs/UPBA_V1_GRID_ECONOMIC_PROFILES.md`. They define price bands, maximum
gross input per fill, and thresholds for when the rational-grid approximation is
small enough for the scoped profile. The checker also emits exact nearest-grid
witnesses for representative rational prices in each band, so the replay
artifact records the finite-grid approximation boundary directly.
It also emits an explicit interval-cover certificate for the whole declared
rational band, binding the assumptions `p_min * D >= 1` and
`ceil(p_max * D) <= max_grid_num` to the nearest-grid epsilon bound.

## Verification Commands

Focused runtime checks:

```bash
pytest -q tests/core/test_uniform_batch_clearing.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py
```

Grid-profile replay:

```bash
python3 tools/upba_v1_grid_economic_profile.py --json
pytest -q tests/tools/test_upba_v1_grid_economic_profile.py
```

Nearby integration checks:

```bash
pytest -q tests/integration/test_dex_engine.py \
  tests/core/test_uniform_batch_clearing.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py \
  tests/core/test_settlement_strong_validator.py \
  tests/core/test_batch_greedy.py
```

Focused Lean check for the standalone UPBA model:

```bash
cd lean-mathlib
~/.elan/bin/lean Proofs/UniformBatchClearingV1.lean
```

`lake env lean Proofs/UniformBatchClearingV1.lean` is the normal project-shaped
checker when the local `external/mathlib4` dependency graph is already hydrated.
The UPBA file has no imports, so the direct Lean command is sufficient for this
standalone proof target.

## Current Non-Claims

UPBA v1 does not currently claim:

- volume-maximizing or surplus-maximizing clearing;
- fair order inclusion;
- censorship resistance;
- oracle-safe mark price construction;
- exact-out support;
- multi-hop support;
- LP add/remove support inside the uniform batch;
- partial-fill support;
- full MEV elimination.

The production-candidate value is narrower and still important: for the scoped
single-pool exact-in surface, the accepted settlement is bound to a deterministic
certificate whose execution and price-objective checks depend on aggregate flow
rather than input order.

## V2 Extension

UPBA v2 is documented separately in `docs/UPBA_V2_CERTIFICATE.md` and
`docs/UPBA_V2_EVIDENCE_BOUNDARY.md`. It preserves the same aggregate-flow price
objective and adds bounded partial fills plus explicit zero-fill rejects under a
new certificate schema and policy id.
