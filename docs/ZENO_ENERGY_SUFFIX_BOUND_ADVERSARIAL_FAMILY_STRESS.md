# ZenoEnergy Suffix-Bound Adversarial Family Stress

This stress injects several verifier-invalid suffix-candidate families after a verifier winner.
Each case compares deterministic suffix certificates with verifier-derived disqualifiers against declared-output-only suffix bounds.

```text
batches: 120
evaluated_batches: 118
skipped_without_winner: 2
candidates_per_batch: 24
seed: 20260545
```

| metric | value |
| --- | ---: |
| family count | 8 |
| total adversarial cases | 944 |
| adversary invalid count | 944 |
| adversary disqualified count | 944 |
| with-disqualifiers certificate ok | 944 |
| without-disqualifiers certificate ok | 590 |
| high-declared-output forced fail | 118 |
| observed disqualifier count | 8 |
| mean suffix disqualified with disqualifiers | 1.0000 |

## Families

- `all_zero`: 118
- `fill_coverage`: 118
- `high_declared_output`: 118
- `limit_violation`: 118
- `negative_reserve`: 118
- `output_mismatch`: 118
- `price_objective`: 118
- `schema_policy`: 118

## Disqualifiers

- `all_zero_fill_vector_flag`: 118
- `fill_coverage_violation_flag`: 118
- `invariant_violation_flag`: 201
- `limit_violation_count`: 117
- `negative_reserve_flag`: 134
- `output_mismatch_count`: 20
- `price_objective_violation_flag`: 118
- `schema_policy_mismatch_flag`: 118

## Negative Knowledge

- High-declared-output suffix adversaries still force failure when deterministic disqualifiers are removed.
- This multi-family stress remains bounded synthetic evidence and does not prove production distribution coverage.
- The stress checks disqualifier mechanics over a supplied finite candidate list, not v2 bounded-grid completeness.
