# ZenoDEX AB Strict Zero-Min Range Step Path Bridge Lean Proof - 2026-06-29

## Executive Result

This artifact adds a recursive range-step path bridge for the AB strict zero-min
subset-mask proof ladder. It chains pruned one-bit transitions over a finite bit
path and proves that the chain induces the existing record-level mask path:

```text
reachablePrunedStepPath parent pathBits child
  -> maskRecordPath parent pathBits child
```

For the full bounded range, Lean proves:

```text
reachablePrunedStepPath parent (List.range bitCount) child
  -> allBitsBelowSet child.maskId bitCount
```

It also packages a recursive range-step child frontier with a selected-family
winner:

```text
rangeStepPathWinnerCertificate parent winner children bitCount masks initialReserveOut suffix
```

The certificate gives both endpoint obligations:

```text
forall child in children, allBitsBelowSet child.maskId bitCount

bestFullSuffixOutputAcrossMasks initialReserveOut children suffix
  <= maskSelectedSuffixOutput initialReserveOut winner suffix
```

This is a direct bridge from one-step induction certificates to a full bounded
range certificate.

## New Lean Surface

File:

```text
lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Added definitions and theorems:

```text
def reachablePrunedStepPath
theorem reachablePrunedStepPath_to_maskRecordPath
theorem reachablePrunedStepPath_pruningInvariant
theorem reachablePrunedStepPath_covers_range_bits
theorem reachablePrunedStepPath_bounds_suffix_output
def reachablePrunedRangeStepPathInFamily
theorem reachablePrunedRangeStepPathInFamily_bounds_family_selected
theorem reachablePrunedRangeStepPathInFamily_covers_and_bounds_family
def reachablePrunedRangeStepPathListInFamily
theorem reachablePrunedRangeStepPathListInFamily_covers_members
theorem reachablePrunedRangeStepPathListInFamily_bounds_family_selected
theorem reachablePrunedRangeStepPathListInFamily_covers_and_bounds_family
def rangeStepPathWinnerCertificate
theorem rangeStepPathWinnerCertificate_covers_and_bounds
theorem witness_rangeStepPathWinnerCertificate_covers_and_bounds
```

The proof reuses the existing bit-mask path lemmas, local pruning dominance,
finite `Nat.max` aggregate bounds, and selected-family winner bridge.

## ZenoDEX Value

The previous artifact proved a one-step induction layer. This artifact chains
those one-step layers over `List.range bitCount`, which is the bounded full-mask
shape used by the existing range endpoint.

For ZenoDEX, this narrows the remaining gap in the AB-ordering research track:
a future checker can consume a recursive range-step certificate and recover full
bounded mask coverage plus one-winner economic dominance. The remaining work is
to connect this certificate language to the concrete compressed DP transition
emitter and final economic key.

## Non-Claims

This artifact does not prove the full strict compressed-DP theorem. It does not
construct the recursive path, child frontier, mask family, or winner. It does
not define tie order. It does not prove that the Python implementation emits
these certificates. It does not prove Lean-to-Python refinement. It does not
cover nonzero `min_amount_out`. It does not prove host bitset equivalence. It
does not authorize settlement, state roots, production promotion, governance
actions, or any consensus-critical path.

## Replay

Expected replay commands:

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 -m json.tool generated/zenodex_ab_strict_zero_min_range_step_path_bridge_lean_20260629/report.json >/dev/null
rg -n "\b(sorry|admit|axiom|unsafe|sorryAx)\b" lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

The final `rg` command should exit with status 1 because no forbidden proof
placeholder is present.

## Research-Kernel Atom

Suggested atom id:

```text
atom_ab_strict_zero_min_range_step_path_bridge_lean_20260629
```

Suggested parents:

```text
atom_ab_strict_zero_min_subset_mask_induction_frontier_20260628
atom_ab_strict_zero_min_step_induction_bridge_lean_20260628
atom_ab_strict_zero_min_compressed_certificate_lean_20260628
```

Suggested status after replay:

```text
SUPPORTED
```
