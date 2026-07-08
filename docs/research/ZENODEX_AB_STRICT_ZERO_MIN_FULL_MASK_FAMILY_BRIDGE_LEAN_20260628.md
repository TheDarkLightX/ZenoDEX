# ZenoDEX AB Strict Zero-Min Full-Mask Family Bridge Lean Proof - 2026-06-28

## Executive Result

This artifact adds a Lean bridge from a reachable pruned range mask to the
finite mask-family aggregate used by the AB strict zero-min subset-DP proof
ladder.

The new predicate makes family membership explicit:

```text
reachablePrunedFullMaskInFamily parent child bitCount masks :=
  reachablePrunedRangeMask parent child bitCount
  and child is a member of masks
```

Lean proves that such a child has both endpoint properties needed by the next
subset-mask induction step:

```text
allBitsBelowSet child.maskId bitCount
```

and

```text
maskFullBestSuffixOutput initialReserveOut child suffix
  <= bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix
```

The value is that the previously proved local endpoint now connects to the
family-level selected-representative aggregate. This is a direct proof
component for the full strict zero-min compressed-DP theorem.

## New Lean Surface

File:

```text
lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Added definitions and theorems:

```text
def reachablePrunedFullMaskInFamily
theorem reachablePrunedFullMaskInFamily_bounds_family_selected
theorem reachablePrunedFullMaskInFamily_covers_and_bounds_family
theorem witness_reachablePrunedFullMaskInFamily_covers_and_bounds_family
```

The proof uses two existing facts:

1. `reachablePrunedRangeMask_bounds_suffix_output`, which bounds the child
   full-record suffix output by the child selected representative.
2. `mem_le_foldlMax`, which lifts a selected representative that appears in
   the mask family to the family selected-representative max.

## ZenoDEX Value

The AB compressed-DP frontier needs to show that a full-mask record family does
not beat the compressed selected representative under strict zero-min
executability. This proof isolates the family endpoint:

```text
local reachable pruned child + child in family
  -> child full-record output <= family selected aggregate
```

That removes one more informal dependency from the future induction theorem.

## Non-Claims

This artifact does not prove the full strict compressed-DP theorem. It does not
construct the mask family. It does not prove that the Python implementation
emits this family. It does not prove canonical tie order. It does not cover
nonzero `min_amount_out`. It does not prove host bitset equivalence. It does not
authorize settlement, state roots, production promotion, governance actions, or
any consensus-critical path.

## Replay

Expected replay commands:

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
rg -n "\b(sorry|admit|axiom|unsafe|sorryAx)\b" lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

The final `rg` command should exit with status 1 because no forbidden proof
placeholder is present.

## Research-Kernel Atom

Suggested atom id:

```text
atom_ab_strict_zero_min_full_mask_family_bridge_lean_20260628
```

Suggested parents:

```text
atom_ab_strict_zero_min_subset_mask_induction_frontier_20260628
atom_ab_strict_zero_min_reachable_pruned_mask_lean_20260628
atom_ab_strict_zero_min_mask_family_pruning_lean_20260628
```

Suggested status after replay:

```text
SUPPORTED
```
