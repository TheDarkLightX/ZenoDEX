# ZenoDEX AB Strict Zero-Min Mask-Path Growth Lean Proof - 2026-06-28

## Executive Result

This artifact extends the AB strict executable zero-min proof ladder from
single-step bit-mask transitions to finite path-growth obligations.

The new path predicate is:

```lean
def allBitsSet (mask : Nat) (pathBits : List Nat) : Prop :=
  forall bitIndex, List.Mem bitIndex pathBits -> maskHasBit mask bitIndex
```

The checked theorem `bitMaskPath_sets_path_bits` proves that every bit named by
a finite `bitMaskPath` is set in the final mask. The record-level theorem
`maskRecordPath_sets_path_bits` connects the same invariant to
`MaskRecordSet.maskId`.

## Value

- Moves the subset-mask induction frontier from one-step preservation to finite
  path growth.
- Gives later compressed-full-mask arguments a reusable statement: start bits
  are preserved, and every newly visited path bit is set in the child mask.
- Keeps the model at the `Nat.testBit` relation layer, avoiding an unverified
  commitment to any host-language bitset implementation.

## Scope

Proved in Lean:

- `allBitsSet` defines the finite path-bit coverage predicate;
- `bitMaskPath_sets_path_bits` proves path bits are set in the final mask;
- `bitMaskPath_preserves_start_or_sets_path_bits` combines prior-bit
  preservation with path-bit growth;
- `maskRecordPath` bridges `MaskRecordSet.maskId` to `bitMaskPath`;
- `maskRecordPath_sets_path_bits` lifts path-bit growth to record masks;
- `maskRecordPath_preserves_parent_bits` lifts parent-bit preservation to record
  masks;
- `witness_bitMaskPath_sets_path_bits` gives a concrete non-vacuity witness.

Non-claims:

- no full strict compressed-full-mask theorem;
- no full DP subset-mask induction;
- no Lean-to-Python refinement proof;
- no canonical tie-order proof;
- no nonzero `min_amount_out` coverage;
- no proof that a concrete host bitset implementation matches this relation;
- no production ordering, settlement, state-root, governance, or promotion
  authority.

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
