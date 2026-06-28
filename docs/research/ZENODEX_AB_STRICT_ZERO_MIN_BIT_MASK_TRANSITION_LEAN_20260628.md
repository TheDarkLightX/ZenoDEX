# ZenoDEX AB Strict Zero-Min Bit-Mask Transition Lean Proof - 2026-06-28

## Executive Result

This artifact extends the AB strict executable zero-min proof ladder with a
bit-level subset-mask transition relation over natural-number masks.

The transition is relational:

```lean
def maskHasBit (mask bitIndex : Nat) : Prop :=
  mask.testBit bitIndex = true

def bitMaskStep (parentMask bitIndex childMask : Nat) : Prop :=
  maskHasBit childMask bitIndex ∧
    ∀ otherBit, otherBit ≠ bitIndex ->
      childMask.testBit otherBit = parentMask.testBit otherBit

def bitMaskPath : Nat -> List Nat -> Nat -> Prop
```

The core lemmas prove that one-bit transitions set the selected bit, preserve
all prior set bits, become extensionally no-op when the selected bit was
already present, and preserve prior bits over a finite path. A record-level
bridge links `MaskRecordSet.maskId` to the same bit-level step relation.

## Value

- Moves the subset-mask frontier from abstract mask identifiers toward a
  bit-level transition relation.
- Gives the later mask-growth induction a reusable transition/path vocabulary.
- Avoids depending on unavailable bit-set helper lemmas by stating the
  transition directly through `Nat.testBit`.

## Scope

Proved in Lean:

- `bitMaskStep` sets the chosen bit in the child mask;
- non-selected bits are preserved by a one-bit step;
- all prior set bits remain set after a one-bit step;
- setting an already-selected bit is extensionally a no-op;
- bit-mask paths preserve prior set bits;
- the head step's bit remains set through the rest of a path;
- `MaskRecordSet.maskId` can be connected to the bit-level step relation;
- concrete no-op transition witness.

Non-claims:

- no full subset-mask growth induction;
- no strict compressed-full-mask theorem;
- no Lean-to-Python refinement proof;
- no canonical tie-order proof;
- no nonzero `min_amount_out` coverage;
- no proof that a concrete host bitset implementation matches this relation;
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
