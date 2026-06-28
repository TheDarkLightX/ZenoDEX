# ZenoDEX AB Strict Zero-Min Reserve-In Sum Lean Proof - 2026-06-28

## Executive Result

This artifact extends the AB strict executable zero-min proof ladder with the
reserve-in subset-sum invariant.

For a fixed exact-in suffix, the final input reserve equals the initial input
reserve plus the sum of gross inputs in that suffix. Therefore two processed
records with the same gross-input sum have the same processed input reserve.

```lean
theorem runReserveInAfterSuffix_eq_reserveInAfterGross
    (initialReserveIn : Nat)
    (steps : List ExactInStep) :
    runReserveInAfterSuffix initialReserveIn steps =
      reserveInAfterGross initialReserveIn steps

theorem sameGrossSum_gives_sameReserveIn
    {initialReserveIn : Nat}
    {left right : List ExactInStep}
    (hsum :
      (left.map ExactInStep.grossIn).sum =
        (right.map ExactInStep.grossIn).sum) :
    reserveInAfterGross initialReserveIn left =
      reserveInAfterGross initialReserveIn right
```

This discharges the reserve-in component of the full one-record compression
frontier. The remaining proof obligations are executable transition modeling,
final reserve-to-surplus connection, subset-mask induction, and refinement to
the Python objective.

## Value

- Separates reserve-in behavior from CPMM output arithmetic.
- Establishes that same processed gross-input sum gives the same processed
  input reserve.
- Supports the existing suffix-dominance and record-set pruning lemmas, which
  compare records that share processed input reserve.

## Scope

Proved in Lean:

- input-reserve execution over a suffix equals initial reserve plus gross-input
  sum;
- append composition for gross-input reserve progression;
- same gross-input sum implies same processed input reserve;
- concrete non-vacuity witnesses for reserve-in execution and equal-sum records.

Non-claims:

- no formal strict executability predicate;
- no sender-balance proof;
- no canonical tie-order proof;
- no nonzero `min_amount_out` coverage;
- no kernel domain-failure proof;
- no full Python subset-DP refinement proof;
- no production ordering or settlement authority.

## Replay

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
```

## Verification

- `lake env lean Proofs/ABStrictZeroMinMonotone.lean`: pass
- `lake build Proofs.ABStrictZeroMinMonotone`: pass
- `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py`: pass
- proof placeholders: none
