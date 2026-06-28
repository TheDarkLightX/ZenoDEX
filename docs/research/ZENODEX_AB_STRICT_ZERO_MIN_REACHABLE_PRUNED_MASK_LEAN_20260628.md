# ZenoDEX AB Strict Zero-Min Reachable Pruned Mask Lean Proof - 2026-06-28

## Executive Result

This artifact adds a Lean bridge for the AB strict zero-min subset-mask frontier.
It packages two already-formalized obligations into one reusable endpoint
predicate:

```text
reachablePrunedRangeMask parent child bitCount :=
  maskRecordPath parent (List.range bitCount) child
  and maskPruningInvariant child
```

For any reachable pruned range mask, Lean proves both endpoint consequences:

```text
allBitsBelowSet child.maskId bitCount
```

and

```text
maskFullBestSuffixOutput initialReserveOut child suffix
  <= maskSelectedSuffixOutput initialReserveOut child suffix
```

The practical value is proof composition. The mask-growth lemma and local
record-pruning lemma now meet at a named endpoint that can be used by the next
subset-mask induction theorem.

## New Lean Surface

File:

```text
lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Added definitions and theorems:

```text
def reachablePrunedRangeMask
theorem reachablePrunedRangeMask_covers_bits
theorem reachablePrunedRangeMask_bounds_suffix_output
theorem reachablePrunedRangeMask_covers_and_bounds
theorem witness_reachablePrunedRangeMask_covers_and_bounds
```

The witness constructs a one-record child mask with `maskId = 1` and proves that
the range path, local pruning invariant, bit coverage, and suffix-output bound
are jointly satisfiable.

## ZenoDEX Value

This proof reduces the next AB-ordering formalization step from coordinating
two independent hypotheses to applying a single endpoint theorem. It is useful
for the strict zero-min compressed-DP line because the target theorem needs both:

1. Range-full mask coverage, so the child mask represents every bit below the
   bounded frontier.
2. Local pruned-representative dominance, so the selected representative is at
   least as good for fixed strict executable suffixes as the full record family.

The result is a bridge theorem, not the final compressed-DP proof.

## Non-Claims

This artifact does not prove the full strict compressed-full-mask theorem. It
does not prove the full DP subset-mask induction. It does not refine the Lean
model to the Python implementation. It does not define canonical tie ordering.
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
atom_ab_strict_zero_min_reachable_pruned_mask_lean_20260628
```

Suggested parents:

```text
atom_ab_strict_zero_min_subset_mask_induction_frontier_20260628
atom_ab_strict_zero_min_range_full_mask_lean_20260628
atom_ab_strict_zero_min_mask_family_pruning_lean_20260628
```

Suggested status after replay:

```text
SUPPORTED
```
