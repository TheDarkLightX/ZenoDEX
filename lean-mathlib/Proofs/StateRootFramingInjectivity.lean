import Mathlib.Tactic

/-!
# State-root framing injectivity

This file records the small Lean theorem behind the state-root v5 FEE-section
hardening. The production encoder is implemented and decoded in Python; the
generic proof obligation is that a decoder which is a left inverse of an
encoder makes that encoder injective. Once the byte-level decoder check
establishes `decode(encode(sections)) = some sections`, two different section
tuples cannot share one preimage.
-/

namespace StateRootFramingInjectivity

structure StateRootV5Sections (Bytes : Type u) where
  bal : Bytes
  pol : Bytes
  lpb : Bytes
  lpa : Bytes
  nnc : Bytes
  fee : Bytes

/-- A left inverse proves injectivity of the encoder. -/
theorem injective_of_left_inverse
    {A : Type u} {B : Type v}
    (encode : A -> B)
    (decode : B -> Option A)
    (hleft : forall x, decode (encode x) = some x) :
    Function.Injective encode := by
  intro x y hxy
  have hx : decode (encode x) = some x := hleft x
  have hy : decode (encode y) = some y := hleft y
  have hsome : (some x : Option A) = some y := by
    calc
      (some x : Option A) = decode (encode x) := hx.symm
      _ = decode (encode y) := by rw [hxy]
      _ = some y := hy
  exact Option.some.inj hsome

/-- If the FEE section differs, the v5 section tuple differs. -/
theorem fee_delta_changes_sections
    {Bytes : Type u}
    {s t : StateRootV5Sections Bytes}
    (hfee : s.fee ≠ t.fee) :
    s ≠ t := by
  intro hst
  exact hfee (by rw [hst])

/--
If the v5 section encoder has a checked left inverse, then changing only the
FEE section changes the encoded preimage.
-/
theorem fee_delta_changes_encoding
    {Bytes : Type u} {Root : Type v}
    (encode : StateRootV5Sections Bytes -> Root)
    (decode : Root -> Option (StateRootV5Sections Bytes))
    (hleft : forall x, decode (encode x) = some x)
    {s t : StateRootV5Sections Bytes}
    (hfee : s.fee ≠ t.fee) :
    encode s ≠ encode t := by
  intro hroot
  have hinj := injective_of_left_inverse encode decode hleft
  have hsections : s = t := hinj hroot
  exact hfee (by rw [hsections])

end StateRootFramingInjectivity
