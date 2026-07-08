# ZenoDEX AB Strict Zero-Min Record-Set Pruning Lean Proof - 2026-06-28

## Executive Result

This artifact extends the AB strict executable zero-min proof line with a
finite record-set pruning theorem.

If a selected compressed record has the minimum output reserve among a finite
set of records that all share the same processed input reserve, then the best
suffix output available from the whole set is no better than continuing from
the selected record.

```lean
theorem bestSuffixOutputFromRecords_le_selected
    {initialReserveOut : Nat}
    {selected : ProcessedRecord}
    {records : List ProcessedRecord}
    {suffix : List ExactInStep}
    (hsame :
      forall record, record in records ->
        selected.processedReserveIn = record.processedReserveIn)
    (hmin :
      forall record, record in records ->
        selected.reserveOut <= record.reserveOut) :
    bestSuffixOutputFromRecords initialReserveOut records suffix <=
      suffixTotalOutput initialReserveOut selected suffix
```

This is the finite-record abstraction of the subset-DP pruning obligation. It
builds on the previously checked suffix-dominance theorem and a `foldl Nat.max`
bound over candidate suffix outputs.

## Value

- Converts pairwise representative dominance into finite candidate-set pruning.
- Narrows the remaining full theorem gap to executable transition modeling,
  subset-mask induction, and refinement to the Python objective.
- Keeps the theorem independent of production ordering or settlement logic.

## Scope

Proved in Lean:

- finite `foldl Nat.max` upper-bound helper;
- best suffix output over a record set is bounded by the selected min-reserve
  representative;
- concrete non-vacuity witness for record-set pruning.

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
