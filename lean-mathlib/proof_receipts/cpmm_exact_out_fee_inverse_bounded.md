# CPMM exact-swap arithmetic, bounded Lean receipt

Date: 2026-05-31

Artifact:

```text
lean-mathlib/Proofs/CPMMExactOutFeeInverse.lean
```

Claims checked:

```text
exactOutFeeInverseBounded 200 = true
exactInSmallDomainSafetyGrid = true
exactOutSmallDomainSafetyGrid = true
```

The fee-inversion theorem is finite over:

```text
1 <= net_in <= 200
0 <= fee_bps < 10000
```

for the runtime exact-out fee formula:

```text
gross_in = ceil(net_in * 10000 / (10000 - fee_bps))
fee_paid = ceil(gross_in * fee_bps / 10000)
gross_in - fee_paid = net_in
```

The exact-in safety grid is finite over:

```text
reserve_in in 1..12
reserve_out in 1..12
amount_in in 1..12
fee_bps in {0, 1, 30, 5000, 9999, 10000}
```

For every formula-accepted case it checks:

```text
k_before <= k_after
new_in = reserve_in + amount_in
new_out = reserve_out - amount_out
amount_out <= reserve_out
```

The exact-out safety grid is finite over:

```text
reserve_in in 1..12
reserve_out in 2..12
amount_out in 1..reserve_out-1
fee_bps in {0, 1, 30, 5000, 9999, 10000}
max_overdelivery_gap_bps = 10000
```

For every formula-accepted case it checks:

```text
amount_out <= amount_out_quote
k_before <= k_after
new_in = reserve_in + gross_in
new_out = reserve_out - amount_out
new_out < reserve_out
```

These mirror the bounded grids in
`tests/runtime/test_cpmm_exact_arithmetic_grid.py` and give the same finite
obligations a Lean-checked replay path. This is finite-domain evidence, not a
full live-domain proof.

## Replay

```bash
lean lean-mathlib/Proofs/CPMMExactOutFeeInverse.lean
lean -R lean-mathlib lean-mathlib/Proofs/CPMMExactOutFeeInverse.lean
```

Result:

```text
exit 0
```

Placeholder scan:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b|unsafe|sorryAx" \
  lean-mathlib/Proofs/CPMMExactOutFeeInverse.lean
```

Result:

```text
no matches
```

## Local Lake Note

`lake env lean Proofs/CPMMExactOutFeeInverse.lean` is not claimed in this
worktree because `lean-mathlib/lakefile.lean` requires
`../external/mathlib4`, and that local dependency is absent here.
