---
title: math_object_innovation_v190
type: note
permalink: autonomous-tau-dex-review/experiments/math-object-innovation-v190
---

# v190 Revenue Surface Atlas

## Structural Target

This cycle narrows FIRE tokenomics from broad "value flow" into concrete
revenue-generating fee surfaces:

```text
revenue_surface_atlas_v1
```

The target is not passive staking yield. The target is a protocol revenue
surface that can fund burn, treasury, proof security, liquidity support, user
rebates, and bounded lock rewards without turning into extraction or wash-trade
farming.

## Bounded Domain

The model evaluates `12` revenue surfaces:

- base swap protocol rake,
- route surplus capture,
- exact-out savings capture,
- COW/batch solver surplus,
- MEV/protection receipts,
- automation orders,
- professional certificate/API use,
- integrator routed flow,
- protocol treasury market-maker bot profit,
- arbitrage recapture auction,
- LP loss-cover premium,
- bounded staking early-exit penalty.

The search enumerates bps parameters for:

- notional fees,
- value-capture fees,
- pro/integrator fees,
- bot profit share,
- insurance premium,
- early-exit penalty,
- solver reward,
- fee rebate and usage reward,
- subsidy emissions,
- sink splits.

## Acceptance Rules

```text
UserNoWorse:
  user_fee_paid <= user_value_created
```

In plain English: a normal fee surface is rejected if the user pays more than
the value the surface creates.

```text
WashNonProfit:
  rebate_or_usage_reward <= fee_paid + execution_drag
```

In plain English: volume/rebate rewards must not make circular self-trading
profitable.

```text
DeflationClaim:
  burn_budget > subsidy_emissions
```

In plain English: lockups and accounting shares are not enough. Total-supply
deflation requires burns to exceed emissions.

```text
PrimaryRevenue:
  primary_recurring_revenue / gross_revenue >= 8500 bps
```

In plain English: the protocol should not depend on penalties, one-off events,
or emergency controls for ordinary revenue.

## Claim Tier

```text
tier = descriptive_oracle
oracle_dependent = true
```

This is a bounded scenario oracle, not a production fee engine or price
forecast. Its role is to reject bad tokenomics shapes before they become
protocol parameters.

## Replay

```bash
python3 experiments/math_object_innovation_v190/run_cycle.py
pytest -q experiments/math_object_innovation_v190/test_cycle.py
julia experiments/math_object_innovation_v190/run_julia_probe.jl
python3 experiments/math_object_innovation_v190/run_mutation_checks.py
python3 experiments/math_object_innovation_v190/check_report_integrity.py
python3 experiments/math_object_innovation_v190/calibrate_receipts.py
```

The Python cycle is the exact replay gate. The Julia probe is a fast discovery
surface for testing parameter ideas before they are promoted into the exact
report.

## Current Result

```text
candidate_policy_count = 155527
survivor_count = 5510
best_survivor = grid_090937_max_burn_guarded
model_audit.total_model_invariant_failures = 0
mutation_receipt.detected_count = 5 / 5
report_integrity.passed_count = 11 / 11
```

Selected best-survivor metrics:

```text
gross_protocol_revenue = 5835
net_protocol_revenue = 5322
total_user_net_value = 2105
burn_budget = 4257
treasury_budget = 266
proof_security_budget = 266
liquidity_budget = 266
lock_reward_budget = 159
deflation_margin = 4257
penalty_dependency_bps = 0
primary_recurring_revenue_bps = 10000
```

The hand-written `fee_surface_launch` policy also survives:

```text
gross_protocol_revenue = 2771
net_protocol_revenue = 2258
total_user_net_value = 3669
burn_budget = 1016
deflation_margin = 1016
```

In plain English: the launch-shaped policy is lower revenue but more user
generous. The grid finds a more aggressive burn-heavy survivor, which should be
treated as a frontier candidate, not as final launch parameters.

## Model-Bug Controls

The cycle includes an internal model audit:

- gross revenue must never be negative,
- user net value must equal `user_value_created - user_fee_paid`,
- net revenue must equal gross revenue minus explicit direct costs,
- sink budgets cannot allocate more than net revenue,
- survivor flags must match the declared acceptance rules,
- named falsifier policies must fail for the expected reason.

The optional Julia probe is an independent implementation of the named-policy
accounting totals. The Python test compares Julia totals against the canonical
Python report when Julia is installed.

The mutation receipt deliberately corrupts model outputs and requires the audit
layer to catch:

- negative gross revenue,
- wrong user-net accounting,
- wrong net-revenue accounting,
- sink-budget over-allocation,
- false survivor flags.

This does not prove the economic assumptions are complete. It proves the current
audit layer is sensitive to the bug classes that are easiest to accidentally
introduce while changing the model.

The report-integrity receipt regenerates the bounded search and compares the
published report against recomputed counts, best survivor, model audit, and
named policy summaries. This catches stale or hand-edited report fields.

The test suite also checks metamorphic laws:

- raising a fee cannot lower total fees from the same policy,
- raising a user-facing fee cannot improve user net value,
- raising rebate/usage rewards cannot lower wash pressure,
- shifting a fixed sink split toward burn cannot lower burn budget,
- bps floor arithmetic obeys zero, full-scale, and monotonic boundaries.

## Receipt Calibration Bridge

The remaining economics gap is the meaning of `MeasuredUserValue`. The
calibration bridge defines a JSONL receipt shape:

```text
schema = zenodex/fire-revenue-surface-receipt/v1
surface
fee_source
notional_units
measured_value_units
user_fee_paid_units
protocol_revenue_units
direct_cost_units
recurring
primary_revenue
wash_score_bps
```

Rows are rejected when user fees exceed measured value, protocol-surplus
capture exceeds surplus, penalties are marked primary, wash score is too high,
or primary revenue is negative after direct costs.

Current fixture replay:

```text
receipt_count = 11
accepted_count = 9
rejected_count = 2
```

The sample fixture is not market data. It is scaffolding for future real
quote/action/API receipts, and it gives the model a typed path from observed
events to empirical value-density caps.
