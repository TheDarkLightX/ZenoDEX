---
title: UPBA V2 Economic Sufficiency V1
type: note
permalink: autonomous-tau-dex-review/docs/upba-v2-economic-sufficiency-v1
---

# UPBA V2 Economic Sufficiency V1

This note defines the first production-candidate policy gate for bounded-grid
UPBA v2 partial-fill economic sufficiency.

The v2 verifier admits partial fills over a fixed admitted intent set. The
economic sufficiency question adds a second approximation axis beyond v1:

```text
price-grid approximation loss
+ fill-vector quantization loss
+ rounding loss
<= declared budget
```

The checker validates that a deployment policy binds both axes with exact
integer arithmetic.

## Game Surface

Players and roles:

- governance or deployment operator proposes a v2 grid policy;
- solver searches price-grid rows and partial-fill vectors;
- verifier accepts only a UPBA v2 certificate for the configured policy;
- policy checker rejects settings whose conservative discretization loss or
  enumeration surface exceeds the declared bounds.

The policy checker is:

```bash
python3 tools/check_upba_v2_grid_policy.py
```

It accepts a policy only for the scoped v2 partial-fill exact-in UPBA lane:

```text
zenodex/upba_v2/fixed_admission_partial_fill_cpmm_exact_in
zenodex/upba_v2_price_fill_grid/partial_fill_exact_in_limit/v1
```

The checker does not extend the claim to exact-out, multi-hop routing, oracle
truth, inclusion fairness, unbounded rational prices, or a scorer that skips
the declared complete fill-vector enumeration.

## Bounded Model

The policy declares:

- pool reserves in atom units;
- token decimals;
- pool fee in bps;
- maximum input per admitted intent;
- maximum total executed input across the batch;
- maximum active intents;
- fill quantum in atom units;
- fill-vector and candidate-evaluation caps;
- raw bounded price-grid dimensions;
- a fixed-denominator economic price ladder inside the raw grid;
- absolute and relative loss budgets.

The raw price grid must fit the existing verifier row cap:

```text
raw_price_grid_row_count :=
  (grid_max_price_num + 1) * (grid_max_price_den + 1)

raw_price_grid_row_count <= UPBA_PRICE_GRID_MAX_ROWS
```

The economic ladder must be contained in the raw grid:

```text
grid_max_price_den >= economic_price_scale
grid_max_price_num >= economic_max_price_scaled
```

The total executed input must be representable by the active-intent cap:

```text
max_total_executed_input_atoms
  <= max_active_intents * max_intent_input_atoms
```

The total executed input must stay inside the declared reserve fraction:

```text
ceil(max_total_executed_input_atoms * 10000
  / min(reserve_base_atoms, reserve_quote_atoms))
  <= max_trade_fraction_bps
```

The fill-vector surface is bounded by the fill quantum:

```text
computed_fill_levels_per_intent :=
  ceil(max_intent_input_atoms / fill_quantum_atoms) + 1

fill_vector_count :=
  computed_fill_levels_per_intent ^ max_active_intents

fill_vector_count <= max_fill_vectors
```

The candidate-evaluation surface binds price rows and fill vectors:

```text
candidate_evaluation_count :=
  raw_price_grid_row_count * fill_vector_count

candidate_evaluation_count <= max_candidate_evaluations
```

The relative-loss denominator must be supported by fee-adjusted notional:

```text
post_fee_input_atoms :=
  floor(max_total_executed_input_atoms * (10000 - fee_bps) / 10000)

min_fee_adjusted_notional_output_atoms :=
  floor(post_fee_input_atoms * economic_min_price_scaled / economic_price_scale)

min_notional_output_atoms <= min_fee_adjusted_notional_output_atoms
```

## Epsilon Bound

The policy composes a price-grid bound and a fill-quantum bound.

```text
half_tick_error_scaled := ceil(economic_tick_size_scaled / 2)

price_grid_loss_atoms :=
  ceil(max_total_executed_input_atoms
    * half_tick_error_scaled
    / economic_price_scale)
```

For partial fills, every active intent can be off by at most half a fill quantum
when projected onto the declared fill lattice. The checker values that residual
at the maximum declared economic price:

```text
half_fill_quantum_atoms := ceil(fill_quantum_atoms / 2)

fill_quantum_loss_atoms :=
  ceil(max_active_intents
    * half_fill_quantum_atoms
    * economic_max_price_scaled
    / economic_price_scale)
```

The accepted absolute budget is:

```text
absolute_loss_bound_atoms :=
  price_grid_loss_atoms
  + fill_quantum_loss_atoms
  + rounding_loss_atoms

absolute_loss_bound_atoms <= max_absolute_loss_atoms
```

The accepted relative budget is:

```text
ceil(absolute_loss_bound_atoms * 1000000 / min_notional_output_atoms)
  <= max_relative_loss_ppm
```

This is a conservative policy rule. It treats every active intent as consuming
the maximum half-quantum residual and prices each residual at the maximum
economic price.

## Restricted Theorem

The Lean packet:

```text
lean-mathlib/Proofs/UPBAV2GridEpsilon.lean
```

records the arithmetic budget bridge:

```text
actual price-grid loss <= price-grid bound
and actual fill-quantum loss <= fill-quantum bound
and price-grid bound + fill-quantum bound + rounding <= budget
-> actual price-grid loss + actual fill-quantum loss + rounding <= budget
```

The two loss premises are economic-model obligations for the configured price
ladder and fill lattice. The checker enforces the right side of the implication
with exact integer arithmetic.

## Evidence Lane

Run the checker on the sample policy:

```bash
python3 tools/check_upba_v2_grid_policy.py
```

Generate and verify a sample JSON policy:

```bash
python3 tools/check_upba_v2_grid_policy.py sample --output /tmp/upba-v2-grid-policy.json
python3 tools/check_upba_v2_grid_policy.py verify /tmp/upba-v2-grid-policy.json
```

Run focused tests:

```bash
pytest -q tests/tools/test_check_upba_v2_grid_policy.py
cd lean-mathlib && lake env lean Proofs/UPBAV2GridEpsilon.lean
pytest -q tests/formal/test_lean_upba_v2_grid_epsilon.py
```

## Promotion Boundary

Accepted claim:

```text
For a declared v2 single-pool partial-fill exact-in UPBA grid policy, the
checker verifies that the bounded price grid contains the declared economic
ladder, that the declared fill lattice has a bounded finite-vector surface, and
that the conservative price-grid plus fill-quantum loss bound is inside the
declared absolute and relative loss budgets.
```

Non-claims:

- unbounded rational optimality;
- every possible market condition;
- exact-out or multi-hop routing;
- oracle truth, fair inclusion, or batch-boundary games;
- production safety for a scorer that omits the declared fill-vector surface;
- full production spot-block ZK scope or production network readiness.
