---
title: math_object_innovation_v191
type: note
permalink: autonomous-tau-dex-review/experiments/math-object-innovation-v191
---

# v191 Fee-Cap Calibration Stress Corpus

## Structural Target

```text
fee_cap_calibration_stress_corpus_v1
```

This cycle stress-tests the v190 receipt-to-cap bridge on a deterministic
multi-sample corpus. The target is not a final fee schedule. The target is a
guardrail: the model should recommend review-stage fee caps only when enough
accepted user-paid receipts exist, should keep penalties and protocol-surplus
captures separate, and should reject known-bad revenue rows.

## Bounded Domain

The generated corpus has `32` rows:

- `6` user-paid fee surfaces,
- `3` accepted samples per user-paid fee surface,
- `2` protocol-surplus internal capture surfaces,
- `1` penalty surface,
- `5` adversarial rows.

The adversarial rows cover:

- user fee greater than measured value,
- protocol surplus capture greater than measured surplus,
- penalty marked as primary revenue,
- high wash score,
- primary revenue with negative net revenue.

## Acceptance Rules

```text
UserFeeCapCandidate:
  accepted_user_fee_samples >= 3
  ∧ user_fee_paid <= measured_user_value
  ∧ recommended_cap <= hard_value_cap
  ∧ launch_parameter_claim = false
```

In plain English: the bridge may emit a review cap only for user-paid surfaces
with enough accepted evidence, and even then it cannot claim the cap is ready
to launch.

```text
BadRowCoverage:
  expected_reject_reason_counts = actual_reject_reason_counts
```

In plain English: each deliberately bad row must fail for the expected reason.

## Claim Tier

```text
tier = descriptive_oracle
oracle_dependent = true
```

The corpus is synthetic. It improves model-bug resistance for the calibration
bridge, but it does not prove economic optimality or market-calibrated launch
fees.

## Replay

```bash
python3 experiments/math_object_innovation_v191/run_cycle.py
pytest -q experiments/math_object_innovation_v191/test_v191_cycle.py
```

## Current Result

```text
receipt_count = 32
accepted_count = 27
rejected_count = 5
candidate_review_cap_count = 6
launch_parameter_claim_count = 0
total_stress_invariant_failures = 0
```

The cap builder clips high observed value fees for:

```text
cow_batch_solver_surplus
lp_loss_cover_premium
```

In plain English: the model sees high-fee non-retail examples, but the
recommendation bridge still clips them to hard value rails and does not promote
them as launch parameters.
