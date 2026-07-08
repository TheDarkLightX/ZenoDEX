# ZenoDEX AB Strict Zero-Min Monotone Reserve Lean Proof

Date: 2026-06-28

## Summary

This artifact adds a Lean proof component for the AB strict executable zero-min
compression research frontier.

For same-pool, same-direction, exact-in CPMM swaps where the future suffix is a
fixed sequence of successful zero-min executions, the proof shows that a lower
current `reserve_out` remains lower after every fixed suffix step. This is the
arithmetic core behind retaining the one record with minimum `reserve_out` for a
processed subset in the experimental compression certificate.

## Proved Component

The checked Lean file is:

```text
lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Main theorem:

```text
runReserveOutAfterSuffix_mono:
  reserveOutSmall <= reserveOutLarge ->
  runReserveOutAfterSuffix reserveIn reserveOutSmall steps <=
  runReserveOutAfterSuffix reserveIn reserveOutLarge steps
```

The proof is built from:

- `postReserveOut_mono_reserveOut`, a one-step CPMM post-reserve monotonicity
  theorem with integer floor rounding.
- `swapOut_contraction` from `CPMMOutputMonotonicity.lean`, which proves that
  adding `delta` output reserve can increase CPMM output by at most `delta`.
- A structural induction over the fixed exact-in suffix.
- `reserveInAfterGross_reverse`, recording that total gross input contribution
  to `reserve_in` is sum-based for a fixed suffix.

## Why It Matters

The previous AB compression evidence was empirical and refuter-backed:

- 330 strict executable zero-min random cases.
- 0 economic-key mismatches against full-state subset DP.
- 80 brute-force cross-checks with 0 mismatches.
- Amount-sorted greedy baselines refuted.

This Lean artifact discharges the rounding-sensitive proof obligation that was
still open in Research Kernel: the retained minimum-`reserve_out` representative
does not lose its dominance under any fixed successful exact-in suffix.

## Non-Claims

This artifact does not prove the full production batch-ordering implementation.
It also does not formalize:

- the strict executability predicate;
- sender balances;
- canonical tie order;
- `min_amount_out > 0` cliffs;
- kernel domain failures;
- the full Python subset-DP implementation;
- production settlement authority.

Those remain host-level, Tau-level, or separate verifier obligations. This file
is a research proof component.

## Verification Receipts

Commands run from the repository root:

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Results:

```text
lake env lean: pass
lake build Proofs.ABStrictZeroMinMonotone: pass
pytest: 1 passed in 8.85s
placeholder scan: No proof placeholders found.
```

## Research Kernel Status

Recommended Research Kernel update:

- Promote the monotone-reserve proof obligation from `UNDER_TEST` to
  `SUPPORTED` as a proof component.
- Keep the full one-record compression exactness claim scoped to strict
  executable zero-min economic keys until strict executability and Python DP
  refinement are separately formalized.
