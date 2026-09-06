import Std.Tactic

/-!
Ordered checked aggregation of signed economic deltas. The accumulator records
each complete (kind, principal, asset, domain) key independently. Each row is
checked after adding it to the preceding rows, before visiting the next row.
The specification quantifies over list splits and exact integer prefix sums;
it is independent of the accumulator implementation.

This is a universal arithmetic model with explicit bounds. The accompanying
finite comparisons exercise the Python fee materializer and route composer,
including their separate stages. They do not establish universal Python/Rust
refinement, input decoding, canonical serialization, metadata preservation,
commit atomicity, cryptography, or publication authority. The function-valued
accumulator abstracts dictionary storage, sorting and zero-row elision.
-/
namespace Proofs.CheckedEconomicAggregationV1

inductive Kind where
  | accountMovement | issue | burn | custody | liability | reserve
  | feeAllocation | reward | slash
  deriving DecidableEq, Repr

structure Key where
  kind : Kind
  principal : String
  asset : String
  domain : String
  deriving DecidableEq, Repr

structure Row where
  key : Key
  delta : Int
  deriving DecidableEq, Repr

structure Bounds where
  lower : Int
  upper : Int
  deriving DecidableEq, Repr

inductive Reject where
  | signedAggregationBounds
  deriving DecidableEq, Repr

abbrev Totals := Key → Int

def empty : Totals := fun _ => 0

def i128 : Bounds :=
  ⟨-170141183460469231731687303715884105728,
    170141183460469231731687303715884105727⟩

def Fits (bounds : Bounds) (value : Int) : Prop :=
  bounds.lower ≤ value ∧ value ≤ bounds.upper

instance (bounds : Bounds) (value : Int) : Decidable (Fits bounds value) :=
  inferInstanceAs (Decidable (_ ∧ _))

def keyedSum (key : Key) : List Row → Int
  | [] => 0
  | row :: rows => (if row.key = key then row.delta else 0) + keyedSum key rows

def advance (initial : Totals) (row : Row) : Totals :=
  fun key => initial key + if row.key = key then row.delta else 0

def checkedFold (bounds : Bounds) (initial : Totals) : List Row → Except Reject Totals
  | [] => .ok initial
  | row :: rows =>
      if Fits bounds (initial row.key + row.delta) then
        checkedFold bounds (advance initial row) rows
      else .error .signedAggregationBounds

/-- Only the key written at this step is checked; untouched keys are irrelevant. -/
def PrefixFits (bounds : Bounds) (initial : Totals) (rows : List Row) : Prop :=
  ∀ (before : List Row) (row : Row) (after : List Row),
    rows = before ++ row :: after →
      Fits bounds (initial row.key + keyedSum row.key before + row.delta)

def mirrorFees : List Row → List Row
  | [] => []
  | row :: rows =>
      if row.key.kind = .feeAllocation then
        row :: ⟨{row.key with kind := .custody}, row.delta⟩ :: mirrorFees rows
      else row :: mirrorFees rows

def checkedMaterialize (bounds : Bounds) (rows : List Row) : Except Reject Totals :=
  checkedFold bounds empty (mirrorFees rows)

def checkedCompose (bounds : Bounds) (spot tokenomics : List Row) : Except Reject Totals :=
  checkedFold bounds empty (spot ++ tokenomics)

theorem i128_bounds_exact :
    i128.lower = -(2 ^ 127 : Int) ∧ i128.upper = (2 ^ 127 : Int) - 1 := by decide

theorem keyedSum_append (key : Key) (left right : List Row) :
    keyedSum key (left ++ right) = keyedSum key left + keyedSum key right := by
  induction left with
  | nil => simp [keyedSum]
  | cons row rows ih => simp only [List.cons_append, keyedSum, ih]; omega

theorem advance_keyed_sum (initial : Totals) (row : Row) (rows : List Row) (key : Key) :
    advance initial row key + keyedSum key rows =
      initial key + keyedSum key (row :: rows) := by
  simp only [advance, keyedSum]
  omega

theorem prefixFits_nil (bounds : Bounds) (initial : Totals) :
    PrefixFits bounds initial [] := by
  intro before row after impossible
  have := congrArg List.length impossible
  simp at this
  omega

theorem prefixFits_cons (bounds : Bounds) (initial : Totals) (head : Row) (tail : List Row) :
    PrefixFits bounds initial (head :: tail) ↔
      Fits bounds (initial head.key + head.delta) ∧
        PrefixFits bounds (advance initial head) tail := by
  constructor
  · intro safe
    constructor
    · simpa [keyedSum] using safe [] head tail rfl
    · intro before row after splitRows
      have bound := safe (head :: before) row after (by simpa using splitRows)
      simpa only [← advance_keyed_sum] using bound
  · rintro ⟨headSafe, tailSafe⟩ before row after splitRows
    cases before with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at splitRows
        rcases splitRows with ⟨rfl, _⟩
        simpa [keyedSum] using headSafe
    | cons first before =>
        simp only [List.cons_append, List.cons.injEq] at splitRows
        rcases splitRows with ⟨rfl, rest⟩
        have bound := tailSafe before row after rest
        simpa only [advance_keyed_sum] using bound

/-- The output equation covers every complete key, including absent and zero keys. -/
theorem checkedFold_ok_iff (bounds : Bounds) (initial : Totals) (rows : List Row)
    (output : Totals) :
    checkedFold bounds initial rows = .ok output ↔
      PrefixFits bounds initial rows ∧
        ∀ key, output key = initial key + keyedSum key rows := by
  induction rows generalizing initial with
  | nil =>
      simp only [checkedFold, Except.ok.injEq, prefixFits_nil, keyedSum, Int.add_zero,
        true_and]
      constructor
      · intro same key; exact congrFun same.symm key
      · intro same; exact (funext same).symm
  | cons row rows ih =>
      rw [checkedFold, prefixFits_cons]
      by_cases fits : Fits bounds (initial row.key + row.delta)
      · rw [if_pos fits, ih]
        simp only [fits, true_and, advance_keyed_sum]
      · simp [fits]

theorem checkedFold_success_iff (bounds : Bounds) (initial : Totals) (rows : List Row) :
    (∃ output, checkedFold bounds initial rows = .ok output) ↔
      PrefixFits bounds initial rows := by
  constructor
  · rintro ⟨output, accepted⟩
    exact ((checkedFold_ok_iff bounds initial rows output).mp accepted).1
  · intro safe
    exact ⟨fun key => initial key + keyedSum key rows,
      (checkedFold_ok_iff bounds initial rows _).mpr ⟨safe, fun _ => rfl⟩⟩

theorem checkedFold_reject_iff (bounds : Bounds) (initial : Totals) (rows : List Row) :
    checkedFold bounds initial rows = .error .signedAggregationBounds ↔
      ¬PrefixFits bounds initial rows := by
  constructor
  · intro rejected safe
    obtain ⟨output, accepted⟩ := (checkedFold_success_iff bounds initial rows).mpr safe
    rw [rejected] at accepted
    contradiction
  · intro bad
    cases result : checkedFold bounds initial rows with
    | ok output => exact False.elim (bad ((checkedFold_success_iff _ _ _).mp ⟨_, result⟩))
    | error reason => cases reason; rfl

theorem successful_complete_keyed_sums (bounds : Bounds) (rows : List Row) (output : Totals)
    (accepted : checkedFold bounds empty rows = .ok output) (key : Key) :
    output key = keyedSum key rows := by
  simpa [empty] using ((checkedFold_ok_iff bounds empty rows output).mp accepted).2 key

theorem materialization_success_iff (bounds : Bounds) (rows : List Row) :
    (∃ output, checkedMaterialize bounds rows = .ok output) ↔
      PrefixFits bounds empty (mirrorFees rows) :=
  checkedFold_success_iff bounds empty (mirrorFees rows)

theorem successful_materialization_keyed_sums (bounds : Bounds) (rows : List Row)
    (output : Totals) (accepted : checkedMaterialize bounds rows = .ok output) (key : Key) :
    output key = keyedSum key (mirrorFees rows) :=
  successful_complete_keyed_sums bounds (mirrorFees rows) output accepted key

theorem out_of_range_prefix_rejects (bounds : Bounds) (initial : Totals)
    (before : List Row) (row : Row) (after : List Row)
    (overflow : ¬Fits bounds (initial row.key + keyedSum row.key before + row.delta)) :
    checkedFold bounds initial (before ++ row :: after) = .error .signedAggregationBounds := by
  apply (checkedFold_reject_iff _ _ _).mpr
  intro safe
  exact overflow (safe before row after rfl)

theorem successful_composition_keyed_sums (bounds : Bounds) (spot tokenomics : List Row)
    (output : Totals) (accepted : checkedCompose bounds spot tokenomics = .ok output)
    (key : Key) : output key = keyedSum key spot + keyedSum key tokenomics := by
  rw [← keyedSum_append]
  exact successful_complete_keyed_sums bounds (spot ++ tokenomics) output accepted key

/-- A representable final sum cannot rescue the upper overflowing second prefix. -/
theorem upper_overflow_cancellation_rejects (key : Key) :
    checkedFold i128 empty [⟨key, i128.upper⟩, ⟨key, 1⟩, ⟨key, -1⟩] =
        .error .signedAggregationBounds ∧
      Fits i128 (keyedSum key [⟨key, i128.upper⟩, ⟨key, 1⟩, ⟨key, -1⟩]) := by
  constructor
  · exact out_of_range_prefix_rejects i128 empty [⟨key, i128.upper⟩] ⟨key, 1⟩
      [⟨key, -1⟩] (by simp [Fits, i128, empty, keyedSum])
  · simp [Fits, i128, keyedSum]

theorem lower_overflow_cancellation_rejects (key : Key) :
    checkedFold i128 empty [⟨key, i128.lower⟩, ⟨key, -1⟩, ⟨key, 1⟩] =
        .error .signedAggregationBounds ∧
      Fits i128 (keyedSum key [⟨key, i128.lower⟩, ⟨key, -1⟩, ⟨key, 1⟩]) := by
  constructor
  · exact out_of_range_prefix_rejects i128 empty [⟨key, i128.lower⟩] ⟨key, -1⟩
      [⟨key, 1⟩] (by simp [Fits, i128, empty, keyedSum])
  · simp [Fits, i128, keyedSum]

/-- Reordering cancellation before the positive increment changes acceptance. -/
theorem cancellation_before_increment_accepts (key : Key) :
    checkedFold i128 empty [⟨key, i128.upper⟩, ⟨key, -1⟩, ⟨key, 1⟩] =
      .ok (advance (advance (advance empty ⟨key, i128.upper⟩) ⟨key, -1⟩) ⟨key, 1⟩) := by
  simp [checkedFold, advance, empty, Fits, i128]

end Proofs.CheckedEconomicAggregationV1
