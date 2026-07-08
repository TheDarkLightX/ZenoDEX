# ZenoDEX AB Strict Zero-Min Suffix Dominance Lean Proof - 2026-06-28

## Executive Result

This artifact extends the AB strict executable zero-min proof line with a
DP-level pruning theorem.

For two records representing the same processed subset, encoded as the same
processed input reserve, the record with lower output reserve gives weakly
greater total extracted output after any fixed strict exact-in suffix.

```lean
theorem minReserveRecord_dominates_suffixTotalOutput
    {initialReserveOut : Nat}
    {lower upper : ProcessedRecord}
    {suffix : List ExactInStep}
    (hsame : lower.processedReserveIn = upper.processedReserveIn)
    (hreserve : lower.reserveOut <= upper.reserveOut) :
    suffixTotalOutput initialReserveOut upper suffix <=
      suffixTotalOutput initialReserveOut lower suffix
```

This is the abstract DP representative-dominance step behind the one-record
min-reserve-out compression certificate. It composes the previously checked
CPMM integer-rounding monotonicity theorem with a lower-final-reserve objective
lemma.

## Value

- Converts the local CPMM monotonicity component into a pruning theorem over
  compressed DP records.
- Reduces the remaining proof gap for strict executable zero-min AB compression:
  the open pieces are now strict executability, canonical scope alignment, and
  full Python refinement rather than the core representative-dominance step.
- Preserves the research boundary. This proof does not authorize production
  ordering, settlement, governance, state roots, or promotion.

## Scope

Proved in Lean:

- fixed-suffix output-reserve monotonicity under integer floor rounding;
- same-processed-subset record dominance when comparing lower vs higher
  output-reserve representatives;
- weakly greater suffix total output for the lower-output-reserve record;
- a concrete non-vacuity witness for the dominance theorem.

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
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
```

## Verification

- `lake env lean Proofs/ABStrictZeroMinMonotone.lean`: pass
- `lake build Proofs.ABStrictZeroMinMonotone`: pass
- `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py`: pass
- proof placeholders: none
