---
title: math_object_innovation_v192
type: note
permalink: autonomous-tau-dex-review/experiments/math-object-innovation-v192
---

# v192 Execution-Derived Fee Receipts

## Structural Target

```text
execution_derived_fee_receipt_bridge_v1
```

This cycle connects the FIRE revenue calibration bridge to actual DEX routing
math. Instead of hand-authoring every measured value, it builds receipts from
the existing CPMM exact-in and exact-out router outputs.

## Bounded Domain

The replay uses:

- `3` deterministic CPMM market cases,
- exact-in amounts: `1000`, `5000`, `10000`,
- exact-out amounts: `500`, `1000`, `5000`,
- `2` deliberately bad execution-derived rows.

For exact-in route surplus:

```text
MeasuredUserValue := best_route_amount_out - direct_route_amount_out
```

For exact-out savings:

```text
MeasuredUserValue := direct_route_amount_in - best_route_amount_in
```

In plain English: the receipt value is the improvement the router actually
finds over the direct route in the same bounded market.

## Acceptance Rules

```text
ExecutionReceiptOK:
  MeasuredUserValue > 0
  ∧ UserFee <= MeasuredUserValue
  ∧ recommended_cap <= 2500 bps for retail surfaces
  ∧ launch_parameter_claim = false
```

In plain English: execution-derived receipts can support review caps only when
the actual router created positive value, the fee is no larger than that value,
and the output remains review-only.

## Claim Tier

```text
tier = descriptive_oracle
oracle_dependent = true
```

The routing arithmetic is real code, but the markets are fixtures. This is not
live market calibration and not a production fee schedule.

## Replay

```bash
python3 experiments/math_object_innovation_v192/run_cycle.py
pytest -q experiments/math_object_innovation_v192/test_v192_cycle.py
```

## Current Result

```text
receipt_count = 20
accepted_count = 18
rejected_count = 2
route_receipt_count = 9
exact_out_receipt_count = 9
candidate_review_cap_count = 2
launch_parameter_claim_count = 0
total_execution_receipt_invariant_failures = 0
```

Measured runtime-derived ranges:

```text
route_improvement_min = 119
route_improvement_max = 7441
exact_out_savings_min = 55
exact_out_savings_max = 4183
```

Review-stage caps:

```text
route_surplus_capture = 2500 bps of measured value
exact_out_savings_capture = 2497 bps of measured value
```

In plain English: the bridge now sees value measured from real router
arithmetic. It still refuses to produce launch parameters and still rejects
tampered over-fee and wash-risk rows.
