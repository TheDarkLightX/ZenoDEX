# ZenoDEX AB Strict Zero-Min Compressed Certificate Lean Proof - 2026-06-28

## Executive Result

This artifact adds a proof-carrying compressed winner certificate for the AB
strict zero-min subset-mask proof ladder. The certificate packages two
previously separated assumptions:

```text
compressedWinnerCertificate parent winner children masks bitCount initialReserveOut suffix :=
  reachablePrunedFullMaskListInFamily parent children bitCount masks
  and selectedFamilyOutputWinner winner masks initialReserveOut suffix
```

Lean proves that one certificate gives both endpoint obligations:

```text
forall child in children, allBitsBelowSet child.maskId bitCount

bestFullSuffixOutputAcrossMasks initialReserveOut children suffix
  <= maskSelectedSuffixOutput initialReserveOut winner suffix
```

This converts the child-list bridge and selected-winner bridge into a single
verifier-facing proof object shape. A checker can require one certificate and
recover child coverage plus selected-winner dominance without replaying the
informal proof ladder.

## New Lean Surface

File:

```text
lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Added definitions and theorems:

```text
def compressedWinnerCertificate
theorem compressedWinnerCertificate_covers_children
theorem compressedWinnerCertificate_bounds_selected_winner
theorem compressedWinnerCertificate_covers_and_bounds
theorem witness_compressedWinnerCertificate_covers_and_bounds
```

The proof is intentionally shallow. It destructures the certificate into the
existing child-list reachability proof and selected-winner proof, then reuses
the already checked endpoint:

```text
reachablePrunedFullMaskListInFamily_covers_and_bounds_selected_winner
```

## ZenoDEX Value

The immediate value is proof-object compression for the AB-ordering research
track. Previous artifacts proved the two sides separately:

1. every full-state child in a finite frontier is represented by a reachable
   pruned selected-mask family;
2. a supplied selected-output winner dominates that selected family.

This artifact defines the shape a future compressed DP verifier can consume:
one certificate, one coverage conclusion, and one economic-dominance
conclusion. That is closer to an auditable witness format for a solver result.

## Non-Claims

This artifact does not prove the full strict compressed-DP theorem. It does not
construct the certificate, child list, selected mask family, or winner. It does
not define tie order. It does not prove the Python implementation emits this
certificate. It does not prove Lean-to-Python refinement. It does not cover
nonzero `min_amount_out`. It does not prove host bitset equivalence. It does
not authorize settlement, state roots, production promotion, governance
actions, or any consensus-critical path.

## Replay

Expected replay commands:

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 -m json.tool generated/zenodex_ab_strict_zero_min_compressed_certificate_lean_20260628/report.json >/dev/null
rg -n "\b(sorry|admit|axiom|unsafe|sorryAx)\b" lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

The final `rg` command should exit with status 1 because no forbidden proof
placeholder is present.

## Research-Kernel Atom

Suggested atom id:

```text
atom_ab_strict_zero_min_compressed_certificate_lean_20260628
```

Suggested parents:

```text
atom_ab_strict_zero_min_subset_mask_induction_frontier_20260628
atom_ab_strict_zero_min_selected_winner_bridge_lean_20260628
atom_ab_strict_zero_min_full_mask_list_bridge_lean_20260628
```

Suggested status after replay:

```text
SUPPORTED
```
