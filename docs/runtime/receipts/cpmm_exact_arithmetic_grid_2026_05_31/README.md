# CPMM exact-swap arithmetic grid

Date: 2026-05-31

This receipt records a deterministic non-Kani evidence slice for the
division-heavy CPMM exact-in/exact-out arithmetic. Kani remains useful for the
small helper contracts, but full symbolic `u128` division was previously
CBMC-intractable. This grid adds independent integer-reference pressure around
the formulas that Kani does not currently prove at live scale.

## Covered finite grids

Exact-in:

```text
reserve_in in 1..12
reserve_out in 1..12
amount_in in 1..12
fee_bps in {0, 1, 30, 5000, 9999, 10000}
```

Total: 10,368 cases.

Exact-out:

```text
reserve_in in 1..12
reserve_out in 2..12
amount_out in 1..reserve_out-1
fee_bps in {0, 1, 30, 5000, 9999, 10000}
max_overdelivery_gap_bps = 10000
```

Total: 4,752 cases.

The tests compare the Python authority against an independent integer reference
for:

- fee ceil rounding;
- exact-in output floor rounding;
- exact-out required net input and gross input ceil rounding;
- overdelivery-gap policy;
- `k_after >= k_before`;
- exact post-reserve shape.

They also run a curated boundary subset through the Rust `cpmm-op` CLI and
compare accepted receipt fields or stable rejection codes.

## Z3 and Lean slices

The test includes a bounded Z3 check for the exact-out fee-inversion identity:

```text
gross_in = ceil(net_in * 10000 / (10000 - fee_bps))
fee_paid = ceil(gross_in * fee_bps / 10000)
gross_in - fee_paid = net_in
```

over:

```text
1 <= net_in <= 200
0 <= fee_bps < 10000
```

This is bounded SMT evidence, not a live-domain theorem.

The same finite identity is mirrored in Lean:

```text
lean-mathlib/Proofs/CPMMExactOutFeeInverse.lean
```

Replay:

```bash
lean lean-mathlib/Proofs/CPMMExactOutFeeInverse.lean
```

Result:

```text
exit 0
```

Receipt:

```text
lean-mathlib/proof_receipts/cpmm_exact_out_fee_inverse_bounded.md
```

## Commands

```bash
python3 -m pytest -q tests/runtime/test_cpmm_exact_arithmetic_grid.py
```

Result:

```text
....                                                                     [100%]
4 passed in 0.55s
```

Focused surrounding CPMM gates:

```bash
python3 -m pytest -q \
  tests/runtime/test_cpmm_exact_arithmetic_grid.py \
  tests/runtime/test_cpmm_settlement_conformance.py \
  tests/runtime/test_cpmm_settlement_disaster_state.py \
  tests/runtime/test_cpmm_settlement_live_path.py \
  tests/runtime/test_cpmm_settlement_semantic_invariants.py
```

Result:

```text
....................                                   [100%]
38 passed in 1.89s
```

Deployment/profile and diff hygiene:

```bash
python3 tools/check_deployment_profiles.py
git diff --check
```

Result:

```text
local-dev: ok
production-strict: ok
public-testnet: ok
```
