# ZenoDEX AB Strict Zero-Min Range Full-Mask Lean Proof - 2026-06-28

## Executive Result

This artifact extends the AB strict executable zero-min proof ladder from
finite path-bit coverage to bounded full-mask coverage over `List.range`.

The new bounded coverage predicate is:

```lean
def allBitsBelowSet (mask bitCount : Nat) : Prop :=
  forall bitIndex, bitIndex < bitCount -> maskHasBit mask bitIndex
```

The checked theorem `bitMaskPath_sets_range_bits` proves that a `bitMaskPath`
whose path list is `List.range bitCount` sets every bit below `bitCount` in the
final mask. The theorem `maskRecordPath_sets_range_bits` lifts the same shape to
`MaskRecordSet.maskId`.

## Value

- Converts the path-growth theorem into the full-range mask form needed by the
  subset-mask induction frontier.
- Separates full-mask coverage from host bitset implementation details by
  staying at the `Nat.testBit` relation layer.
- Gives the next compressed-full-mask proof attempt a small reusable statement:
  a range-ordered path covers every bounded bit index.

## Scope

Proved in Lean:

- `allBitsBelowSet` defines bounded bit coverage;
- `allBitsSet_range_gives_allBitsBelowSet` bridges `List.range` membership to
  bounded coverage;
- `bitMaskPath_sets_range_bits` proves range paths set every bounded bit;
- `maskRecordPath_sets_range_bits` lifts range coverage to record mask ids;
- `witness_bitMaskPath_sets_range_bits` gives a concrete non-vacuity witness.

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
