# ZenoEnergy Suffix-Bound Adversarial Stress

This stress injects high-declared-output invalid candidates into the unchecked suffix.
It compares deterministic suffix certificates with verifier-derived disqualifiers against declared-output-only suffix bounds.

```text
batches: 120
evaluated_batches: 119
skipped_without_winner: 1
candidates_per_batch: 24
seed: 20260544
```

| metric | value |
| --- | ---: |
| adversary invalid count | 119 |
| adversary disqualified count | 119 |
| with-disqualifiers certificate ok | 119 |
| without-disqualifiers certificate ok | 0 |
| declared-output-only forced fail | 119 |
| mean suffix disqualified with disqualifiers | 20.1933 |

## Disqualifiers

- `invariant_violation_flag`: 119

## Negative Knowledge

- Declared-output suffix bounds alone fail on every injected adversarial suffix case.
- This stress remains bounded synthetic evidence and does not prove production distribution coverage.
