import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# FIRE Strict Settlement Authority Boundary

This file models the runtime parser rule used by the FIRE authority receipt
boundary:

* settlement deltas must decode as exact integers;
* booleans, strings, and missing fields do not decode;
* authority acceptance may only be derived after successful strict decoding.

The Python implementation enforces this in `src/fire/runtime/common_v1.py` and
`src/fire/kernel/persisted_bundle_settlement_v1.py`.  The theorem here records
the proof-side contract: no receipt-authority proof can be built from coerced
string-shaped or boolean-shaped deltas.
-/

namespace Proofs
namespace FIREStrictSettlementAuthority

/-- A tiny model of the untrusted boundary values relevant to settlement deltas. -/
inductive RawValue where
  | int : Int -> RawValue
  | bool : Bool -> RawValue
  | str : String -> RawValue
  | missing : RawValue
  deriving DecidableEq, Repr

/-- Strict integer decoding: only an actual integer field is accepted. -/
def strictInt : RawValue -> Option Int
  | RawValue.int n => some n
  | RawValue.bool _ => none
  | RawValue.str _ => none
  | RawValue.missing => none

structure RawSettlementState where
  holderDelta : RawValue
  writerDelta : RawValue
  deriving DecidableEq, Repr

structure SettlementDeltas where
  holderDelta : Int
  writerDelta : Int
  deriving DecidableEq, Repr

/-- Decode both deltas, failing closed if either side is not an exact integer. -/
def decodeSettlementDeltas (raw : RawSettlementState) : Option SettlementDeltas := do
  let holder <- strictInt raw.holderDelta
  let writer <- strictInt raw.writerDelta
  pure { holderDelta := holder, writerDelta := writer }

/-- Authority receipt construction requires strict decoded deltas and conservation. -/
def SettlementAuthorityAccepts (raw : RawSettlementState) : Prop :=
  ∃ deltas,
    decodeSettlementDeltas raw = some deltas ∧
      deltas.holderDelta + deltas.writerDelta = 0

theorem strictInt_some_implies_raw_int
    {raw : RawValue} {n : Int}
  (h : strictInt raw = some n) :
    raw = RawValue.int n := by
  cases raw <;> simp [strictInt] at h ⊢
  exact h

theorem decode_some_implies_raw_holder_int
    {raw : RawSettlementState} {deltas : SettlementDeltas}
    (h : decodeSettlementDeltas raw = some deltas) :
    raw.holderDelta = RawValue.int deltas.holderDelta := by
  unfold decodeSettlementDeltas at h
  cases hh : strictInt raw.holderDelta with
  | none =>
      simp [hh] at h
  | some holder =>
      cases hw : strictInt raw.writerDelta with
      | none =>
          simp [hh, hw] at h
      | some writer =>
          simp [hh, hw] at h
          rcases h with ⟨rfl, _rfl⟩
          exact strictInt_some_implies_raw_int hh

theorem decode_some_implies_raw_writer_int
    {raw : RawSettlementState} {deltas : SettlementDeltas}
    (h : decodeSettlementDeltas raw = some deltas) :
    raw.writerDelta = RawValue.int deltas.writerDelta := by
  unfold decodeSettlementDeltas at h
  cases hh : strictInt raw.holderDelta with
  | none =>
      simp [hh] at h
  | some holder =>
      cases hw : strictInt raw.writerDelta with
      | none =>
          simp [hh, hw] at h
      | some writer =>
          simp [hh, hw] at h
          rcases h with ⟨_rfl, rfl⟩
          exact strictInt_some_implies_raw_int hw

/-- Accepted settlement authority implies both untrusted delta fields were true integers. -/
theorem authority_accept_implies_raw_deltas_int
    {raw : RawSettlementState}
    (h : SettlementAuthorityAccepts raw) :
    (∃ holder, raw.holderDelta = RawValue.int holder) ∧
      (∃ writer, raw.writerDelta = RawValue.int writer) := by
  rcases h with ⟨deltas, hdecode, _hconserved⟩
  exact ⟨
    ⟨deltas.holderDelta, decode_some_implies_raw_holder_int hdecode⟩,
    ⟨deltas.writerDelta, decode_some_implies_raw_writer_int hdecode⟩
  ⟩

/-- A string-shaped holder delta cannot authorize settlement, even if it looks numeric. -/
theorem string_holder_delta_not_authorized
    (s : String) (writer : Int) :
    ¬ SettlementAuthorityAccepts
      { holderDelta := RawValue.str s, writerDelta := RawValue.int writer } := by
  intro h
  rcases authority_accept_implies_raw_deltas_int h with ⟨⟨holder, hholder⟩, _⟩
  cases hholder

/-- A boolean-shaped writer delta cannot authorize settlement. -/
theorem bool_writer_delta_not_authorized
    (holder : Int) (b : Bool) :
    ¬ SettlementAuthorityAccepts
      { holderDelta := RawValue.int holder, writerDelta := RawValue.bool b } := by
  intro h
  rcases authority_accept_implies_raw_deltas_int h with ⟨_, ⟨writer, hwriter⟩⟩
  cases hwriter

/-- Missing deltas cannot authorize settlement. -/
theorem missing_holder_delta_not_authorized
    (writer : Int) :
    ¬ SettlementAuthorityAccepts
      { holderDelta := RawValue.missing, writerDelta := RawValue.int writer } := by
  intro h
  rcases authority_accept_implies_raw_deltas_int h with ⟨⟨holder, hholder⟩, _⟩
  cases hholder

end FIREStrictSettlementAuthority
end Proofs
