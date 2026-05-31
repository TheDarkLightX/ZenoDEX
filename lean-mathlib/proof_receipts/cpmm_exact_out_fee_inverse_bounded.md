# CPMM exact-out fee inversion, bounded Lean receipt

Date: 2026-05-31

Artifact:

```text
lean-mathlib/Proofs/CPMMExactOutFeeInverse.lean
```

Claim checked:

```text
exactOutFeeInverseBounded 200 = true
```

This is a finite Lean theorem over:

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

This mirrors the Z3 obligation in
`tests/runtime/test_cpmm_exact_arithmetic_grid.py` and gives the same bounded
identity a Lean-checked replay path. It is finite-domain evidence, not a full
live-domain proof.

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
