# ZenoDEX AB Strict Zero-Min Mask-Family Pruning Lean Proof - 2026-06-28

## Executive Result

This artifact extends the AB strict executable zero-min proof ladder with a
finite subset-mask aggregation component.

Given a finite family of abstract subset masks, if each mask's compressed
representative has the same processed input reserve as every full-state record
at that mask and no more output reserve, then the best suffix output available
from all full-state records across the mask family is bounded by the best suffix
output from the compressed representatives:

```lean
theorem bestFullSuffixOutputAcrossMasks_le_selected
    {initialReserveOut : Nat}
    {masks : List MaskRecordSet}
    {suffix : List ExactInStep}
    (hinvariant : forall mask, List.Mem mask masks -> maskPruningInvariant mask) :
    bestFullSuffixOutputAcrossMasks initialReserveOut masks suffix <=
      bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix
```

This is the mask-family aggregation step for the narrowed subset-mask induction
frontier. It reuses the existing finite record-set pruning theorem at each mask
and proves that the `Nat.max` aggregation across masks preserves the pruning
bound.

## Value

- Lifts local per-mask representative dominance to a finite family of masks.
- Separates aggregation across masks from the remaining transition-relation
  induction.
- Provides reusable max-fold helper lemmas for later subset-DP proof work.

## Scope

Proved in Lean:

- `Nat.max` fold lower-bounds its accumulator;
- every member of a finite max-fold is bounded by the fold result;
- local mask pruning bounds full records at one mask by the selected
  representative;
- local pruning invariants across all masks bound the full-state mask-family
  best by the compressed-representative mask-family best;
- concrete non-vacuity witness for a two-mask family.

Non-claims:

- no bit-level subset-mask transition relation;
- no mask-growth induction proof;
- no strict compressed-full-mask theorem;
- no Lean-to-Python refinement proof;
- no canonical tie-order proof;
- no nonzero `min_amount_out` coverage;
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
