# ZenoDEX AB Strict Zero-Min Selected Winner Bridge Lean Proof - 2026-06-28

## Executive Result

This artifact adds the selected-winner bridge for the AB strict zero-min
subset-mask proof ladder. It collapses the selected-family aggregate to one
supplied compressed representative.

The new predicate states that a winner dominates every selected representative
in a finite mask family:

```text
selectedFamilyOutputWinner winner masks initialReserveOut suffix :=
  winner is a member of masks
  and every mask in masks has selected suffix output <= winner selected suffix output
```

Lean proves:

```text
bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix
  <= maskSelectedSuffixOutput initialReserveOut winner suffix
```

and composes this with the finite child-list bridge:

```text
reachablePrunedFullMaskListInFamily parent children bitCount masks
and selectedFamilyOutputWinner winner masks initialReserveOut suffix
  -> bestFullSuffixOutputAcrossMasks initialReserveOut children suffix
     <= maskSelectedSuffixOutput initialReserveOut winner suffix
```

The result is a concrete compressed-representative endpoint for the proof
frontier.

## New Lean Surface

File:

```text
lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Added definitions and theorems:

```text
def selectedFamilyOutputWinner
theorem selectedFamilyOutputWinner_bounds_selected_family
theorem reachablePrunedFullMaskListInFamily_bounds_selected_winner
theorem reachablePrunedFullMaskListInFamily_covers_and_bounds_selected_winner
theorem witness_reachablePrunedFullMaskListInFamily_bounds_selected_winner
```

The proof uses `foldlMax_le_bound` to bound the selected-family max by the
supplied winner, then composes that result with the finite child-list bridge.

## ZenoDEX Value

The previous proof component bounded the full child-frontier list by the
selected-family aggregate. This bridge shows how that aggregate reduces to one
compressed representative once a winner certificate is supplied.

That is closer to the form needed by a compressed DP certificate: a verifier can
check a winner-dominance obligation separately from the proof that full-state
children are dominated by the selected family.

## Non-Claims

This artifact does not prove the full strict compressed-DP theorem. It does not
construct the winner. It does not define tie order. It does not construct the
child list or the selected mask family. It does not prove that the Python
implementation emits the winner or the family. It does not cover nonzero
`min_amount_out`. It does not prove host bitset equivalence. It does not
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
atom_ab_strict_zero_min_selected_winner_bridge_lean_20260628
```

Suggested parents:

```text
atom_ab_strict_zero_min_subset_mask_induction_frontier_20260628
atom_ab_strict_zero_min_full_mask_list_bridge_lean_20260628
atom_ab_strict_zero_min_full_mask_family_bridge_lean_20260628
```

Suggested status after replay:

```text
SUPPORTED
```
