---
title: UPBA Economic Sufficiency V1
type: note
permalink: autonomous-tau-dex-review/docs/upba-economic-sufficiency-v1
---

# UPBA Economic Sufficiency V1

This note defines the first production-candidate policy gate for bounded-grid
UPBA economic sufficiency.

The existing bounded price-grid verifier proves a precise statement:

```text
complete bounded grid evidence
and winner dominates every row
-> winner is weakly optimal over the configured bounded grid
```

That is a formal finite-grid claim. It still needs a deployment policy saying
the chosen grid is economically tight enough for the pool, reserves, fee,
decimals, and max trade size being admitted.

## Game Surface

Players and roles:

- governance or deployment operator proposes a bounded-grid policy;
- solver builds UPBA candidate rows inside that grid;
- verifier checks finite-grid optimality;
- policy checker rejects grid settings whose worst-case discretization loss is
  above the declared economic budget.

The policy checker is:

```bash
python3 tools/check_upba_grid_policy.py
```

It accepts a policy only for the current v1 full-fill exact-in UPBA grid scorer and requires `trade_direction = base_to_quote`:

```text
zenodex/upba_v1/fixed_admission_full_fill_cpmm_exact_in
zenodex/upba_price_grid/full_fill_exact_in_limit/v1
```

It does not extend the claim to UPBA v2 partial fills, exact-out, multi-hop,
oracle fairness, inclusion fairness, or unbounded rational prices.

## Bounded Model

The policy declares:

- trade direction (`base_to_quote` only for this v1 checker);

- pool reserves in atom units;
- token decimals;
- pool fee in bps;
- maximum admitted trade input in atom units;
- maximum trade size as a fraction of the smaller reserve;
- raw bounded-grid dimensions;
- a fixed-denominator economic ladder inside the raw grid;
- absolute and relative loss budgets.

The checker uses exact integer arithmetic only.

```text
raw_grid_row_count :=
  (grid_max_price_num + 1) * (grid_max_price_den + 1)
```

The raw grid must fit the verifier row cap:

```text
raw_grid_row_count <= UPBA_PRICE_GRID_MAX_ROWS
```

The economic ladder must be contained in the raw grid:

```text
grid_max_price_den >= economic_price_scale
grid_max_price_num >= economic_max_price_scaled
```

The max trade must stay inside the declared reserve fraction:

```text
ceil(max_trade_input_atoms * 10000 / min(reserve_base_atoms, reserve_quote_atoms))
  <= max_trade_fraction_bps
```

The relative-loss denominator must also be supported by the declared fee and
minimum economic price:

```text
post_fee_input_atoms :=
  floor(max_trade_input_atoms * (10000 - fee_bps) / 10000)

min_fee_adjusted_notional_output_atoms :=
  floor(post_fee_input_atoms * economic_min_price_scaled / economic_price_scale)

min_notional_output_atoms <= min_fee_adjusted_notional_output_atoms
```

## Epsilon Bound

The policy uses a fixed-denominator ladder with scale
`economic_price_scale` and tick size `economic_tick_size_scaled`.

```text
half_tick_error_scaled := ceil(economic_tick_size_scaled / 2)

raw_grid_loss_atoms :=
  ceil(max_trade_input_atoms * half_tick_error_scaled / economic_price_scale)

absolute_loss_bound_atoms :=
  raw_grid_loss_atoms + rounding_loss_atoms
```

The checker accepts only when:

```text
absolute_loss_bound_atoms <= max_absolute_loss_atoms
```

and:

```text
ceil(absolute_loss_bound_atoms * 1000000 / min_notional_output_atoms)
  <= max_relative_loss_ppm
```

The formula is deliberately conservative. It treats the price tick as the full
declared economic tick even though the raw bounded grid may include additional
rational pairs that improve the actual search.

## Restricted Theorem

The Lean packet:

```text
lean-mathlib/Proofs/UPBAGridEpsilon.lean
```

records the arithmetic budget bridge:

```text
actual grid loss <= ceil(max input * half tick / scale)
and ceil(max input * half tick / scale) + rounding <= budget
-> actual grid loss + rounding <= budget
```

The premise `actual grid loss <= ...` is the economic-model obligation for the
fixed-denominator ladder. The checker enforces the right side of the implication
with exact integer arithmetic.

## Evidence Lane

Run the checker on the sample policy:

```bash
python3 tools/check_upba_grid_policy.py
```

Generate and verify a sample JSON policy:

```bash
python3 tools/check_upba_grid_policy.py sample --output /tmp/upba-grid-policy.json
python3 tools/check_upba_grid_policy.py verify /tmp/upba-grid-policy.json
```

Run focused tests:

```bash
pytest -q tests/tools/test_check_upba_grid_policy.py
cd lean-mathlib && lake env lean Proofs/UPBAGridEpsilon.lean
pytest -q tests/formal/test_lean_upba_grid_epsilon.py
```

## Promotion Boundary

Accepted claim:

```text
For a declared v1 single-pool full-fill exact-in UPBA grid policy, the checker
verifies that the bounded grid contains the declared economic ladder and that
the conservative tick-loss bound is inside the declared absolute and relative
loss budgets.
```

Non-claims:

- unbounded rational optimality;
- every possible market condition;
- UPBA v2 partial-fill economic sufficiency;
- exact-out or multi-hop routing;
- oracle truth, fair inclusion, or batch-boundary games.
