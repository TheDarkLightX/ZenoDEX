import Mathlib.Data.Int.Basic
import Mathlib.Data.String.Basic
import Mathlib.Tactic

/-!
# FIRE Strict Spec Parsing Boundary

This file models the strict text-field rule used by FIRE math-object spec
loading.  The runtime parser rejects numeric, boolean, missing, and empty values
for canonical textual fields such as schema, object id, units, and expression
kinds.

The theorem surface is deliberately small: it proves that any accepted FMOS
header has actual non-empty text at the raw boundary, and that numeric/boolean/
missing raw values cannot satisfy the text-field acceptance rule.
-/

namespace Proofs
namespace FIREStrictSpecParsing

/-- Tiny model of raw JSON-like scalar values at the spec boundary. -/
inductive RawScalar where
  | text : String -> RawScalar
  | int : Int -> RawScalar
  | bool : Bool -> RawScalar
  | missing : RawScalar
  deriving DecidableEq, Repr

/-- Strict non-empty text decoding: no numeric/bool/missing coercion. -/
def strictNonemptyText : RawScalar -> Option String
  | RawScalar.text s => if s.isEmpty then none else some s
  | RawScalar.int _ => none
  | RawScalar.bool _ => none
  | RawScalar.missing => none

/-- A raw field is accepted as text exactly when strict decoding succeeds. -/
def TextFieldAccepts (raw : RawScalar) : Prop :=
  ∃ s, strictNonemptyText raw = some s

theorem strictNonemptyText_some_implies_raw_text
    {raw : RawScalar} {s : String}
    (h : strictNonemptyText raw = some s) :
    raw = RawScalar.text s := by
  cases raw with
  | text t =>
      unfold strictNonemptyText at h
      by_cases ht : t.isEmpty
      · simp [ht] at h
      · simp [ht] at h
        cases h
        rfl
  | int n =>
      simp [strictNonemptyText] at h
  | bool b =>
      simp [strictNonemptyText] at h
  | missing =>
      simp [strictNonemptyText] at h

theorem text_field_accept_implies_raw_text
    {raw : RawScalar}
    (h : TextFieldAccepts raw) :
    ∃ s, raw = RawScalar.text s := by
  rcases h with ⟨s, hs⟩
  exact ⟨s, strictNonemptyText_some_implies_raw_text hs⟩

theorem int_field_not_accepted (n : Int) :
    ¬ TextFieldAccepts (RawScalar.int n) := by
  intro h
  rcases h with ⟨s, hs⟩
  simp [strictNonemptyText] at hs

theorem bool_field_not_accepted (b : Bool) :
    ¬ TextFieldAccepts (RawScalar.bool b) := by
  intro h
  rcases h with ⟨s, hs⟩
  simp [strictNonemptyText] at hs

theorem missing_field_not_accepted :
    ¬ TextFieldAccepts RawScalar.missing := by
  intro h
  rcases h with ⟨s, hs⟩
  simp [strictNonemptyText] at hs

theorem empty_text_field_not_accepted :
    ¬ TextFieldAccepts (RawScalar.text "") := by
  intro h
  rcases h with ⟨s, hs⟩
  have hEmpty : "".isEmpty = true := rfl
  simp [strictNonemptyText, hEmpty] at hs

/-- Raw subset of canonical FMOS header fields hardened by the loader. -/
structure RawFMOSHeader where
  schema : RawScalar
  objectId : RawScalar
  objectName : RawScalar
  objectVersion : RawScalar
  objectFamily : RawScalar
  settlementAsset : RawScalar
  irHash : RawScalar
  deriving DecidableEq, Repr

/-- The header is accepted only when every canonical text field decodes
strictly and the schema equals the expected schema. -/
def FMOSHeaderAccepts (expectedSchema : String) (raw : RawFMOSHeader) : Prop :=
  ∃ schema objectId objectName objectVersion objectFamily settlementAsset irHash,
    strictNonemptyText raw.schema = some schema ∧
      schema = expectedSchema ∧
      strictNonemptyText raw.objectId = some objectId ∧
      strictNonemptyText raw.objectName = some objectName ∧
      strictNonemptyText raw.objectVersion = some objectVersion ∧
      strictNonemptyText raw.objectFamily = some objectFamily ∧
      strictNonemptyText raw.settlementAsset = some settlementAsset ∧
      strictNonemptyText raw.irHash = some irHash

/-- FMOS header acceptance implies all canonical raw fields were real text
fields, not coerced numbers/bools/missing values. -/
theorem fmos_header_accept_implies_text_fields
    {expectedSchema : String} {raw : RawFMOSHeader}
    (h : FMOSHeaderAccepts expectedSchema raw) :
    (∃ s, raw.schema = RawScalar.text s) ∧
      (∃ s, raw.objectId = RawScalar.text s) ∧
      (∃ s, raw.objectName = RawScalar.text s) ∧
      (∃ s, raw.objectVersion = RawScalar.text s) ∧
      (∃ s, raw.objectFamily = RawScalar.text s) ∧
      (∃ s, raw.settlementAsset = RawScalar.text s) ∧
      (∃ s, raw.irHash = RawScalar.text s) := by
  rcases h with
    ⟨schema, objectId, objectName, objectVersion, objectFamily, settlementAsset, irHash,
      hSchema, _hExpected, hObjectId, hObjectName, hObjectVersion, hObjectFamily,
      hSettlementAsset, hIrHash⟩
  exact ⟨
    ⟨schema, strictNonemptyText_some_implies_raw_text hSchema⟩,
    ⟨objectId, strictNonemptyText_some_implies_raw_text hObjectId⟩,
    ⟨objectName, strictNonemptyText_some_implies_raw_text hObjectName⟩,
    ⟨objectVersion, strictNonemptyText_some_implies_raw_text hObjectVersion⟩,
    ⟨objectFamily, strictNonemptyText_some_implies_raw_text hObjectFamily⟩,
    ⟨settlementAsset, strictNonemptyText_some_implies_raw_text hSettlementAsset⟩,
    ⟨irHash, strictNonemptyText_some_implies_raw_text hIrHash⟩
  ⟩

theorem int_schema_header_not_accepted
    (expectedSchema : String)
    (n : Int)
    (objectId objectName objectVersion objectFamily settlementAsset irHash : RawScalar) :
    ¬ FMOSHeaderAccepts expectedSchema
      { schema := RawScalar.int n,
        objectId := objectId,
        objectName := objectName,
        objectVersion := objectVersion,
        objectFamily := objectFamily,
        settlementAsset := settlementAsset,
        irHash := irHash } := by
  intro h
  rcases h with ⟨schema, _objectId, _objectName, _objectVersion, _objectFamily, _settlementAsset, _irHash,
    hSchema, _rest⟩
  simp [strictNonemptyText] at hSchema

end FIREStrictSpecParsing
end Proofs
