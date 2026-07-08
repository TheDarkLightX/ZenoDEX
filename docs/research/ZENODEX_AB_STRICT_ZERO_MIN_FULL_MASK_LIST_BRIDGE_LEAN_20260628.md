# ZenoDEX AB Strict Zero-Min Full-Mask List Bridge Lean Proof - 2026-06-28

## Executive Result

This artifact lifts the single reachable full-mask family bridge to a finite
list of reachable pruned full-mask children.

The new predicate states that every child in a list is a reachable pruned
full-mask member of the selected mask family:

```text
reachablePrunedFullMaskListInFamily parent children bitCount masks :=
  for every child in children,
    reachablePrunedFullMaskInFamily parent child bitCount masks
```

Lean proves two list-level consequences:

```text
for every child in children:
  allBitsBelowSet child.maskId bitCount
```

and

```text
bestFullSuffixOutputAcrossMasks initialReserveOut children suffix
  <= bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix
```

This is a direct finite-family lift toward the AB strict zero-min subset-mask
induction theorem. It replaces per-child reasoning with one reusable list-level
endpoint.

## New Lean Surface

File:

```text
lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Added definitions and theorems:

```text
def reachablePrunedFullMaskListInFamily
theorem reachablePrunedFullMaskListInFamily_covers_members
theorem reachablePrunedFullMaskListInFamily_bounds_family_selected
theorem reachablePrunedFullMaskListInFamily_covers_and_bounds_family
theorem witness_reachablePrunedFullMaskListInFamily_covers_and_bounds_family
```

The proof uses `foldlMax_le_bound` to lift the single-child selected-family
bound over the finite child list.

## ZenoDEX Value

The compressed-DP proof frontier eventually needs to reason about a finite
collection of candidate full-state masks. This proof shows that if every
candidate child has already been retained as a reachable pruned full-mask member
of the selected family, then the full candidate list cannot beat the selected
family aggregate.

This is useful because it aligns the proof obligation with the data structure
shape used by dynamic programming: finite frontiers of records and masks.

## Non-Claims

This artifact does not prove the full strict compressed-DP theorem. It does not
construct the child list or the selected mask family. It does not prove that the
Python implementation emits either list. It does not prove canonical tie order.
It does not cover nonzero `min_amount_out`. It does not prove host bitset
equivalence. It does not authorize settlement, state roots, production
promotion, governance actions, or any consensus-critical path.

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
atom_ab_strict_zero_min_full_mask_list_bridge_lean_20260628
```

Suggested parents:

```text
atom_ab_strict_zero_min_subset_mask_induction_frontier_20260628
atom_ab_strict_zero_min_full_mask_family_bridge_lean_20260628
atom_ab_strict_zero_min_reachable_pruned_mask_lean_20260628
```

Suggested status after replay:

```text
SUPPORTED
```
