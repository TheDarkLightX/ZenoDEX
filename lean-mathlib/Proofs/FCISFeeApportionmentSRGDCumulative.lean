import Proofs.FCISFeeApportionmentSRGDAdaptiveTrace
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace FCISFeeApportionmentSRGDCumulative

open FCISFeeApportionmentSRGD
open FCISFeeApportionmentSRGDAdaptiveTrace

/-- One role's actual atom contribution and integer allocation count. -/
structure HistoryContribution where
  actual : Int
  allocation : Int

def zeroHistory : HistoryContribution :=
  { actual := 0, allocation := 0 }

def addHistory (left right : HistoryContribution) : HistoryContribution :=
  { actual := left.actual + right.actual
    allocation := left.allocation + right.allocation }

def actualSum : List HistoryContribution → Int
  | [] => 0
  | contribution :: rest => contribution.actual + actualSum rest

def allocationSum : List HistoryContribution → Int
  | [] => 0
  | contribution :: rest => contribution.allocation + allocationSum rest

/-- The integer discrepancy numerator for one complete history. -/
def historyDeficit (D : Int) (history : List HistoryContribution) : Int :=
  actualSum history - D * allocationSum history

/-- Apply one historical contribution to the integer discrepancy state. -/
def applyHistory (D state : Int) (contribution : HistoryContribution) : Int :=
  state + contribution.actual - D * contribution.allocation

/-- Fold a history in its supplied order. -/
def foldHistory (D : Int) (history : List HistoryContribution) (initial : Int) : Int :=
  history.foldl (fun state contribution => applyHistory D state contribution) initial

/-- The complete history identity, with an explicit initial state. -/
theorem history_identity
    (D : Int)
    (history : List HistoryContribution)
    (initial : Int) :
    foldHistory D history initial =
      initial + historyDeficit D history := by
  induction history generalizing initial with
  | nil =>
      simp [foldHistory, historyDeficit, actualSum, allocationSum]
  | cons contribution rest ih =>
      change foldHistory D rest (applyHistory D initial contribution) =
        initial + historyDeficit D (contribution :: rest)
      rw [ih]
      simp [historyDeficit, actualSum, allocationSum, applyHistory, Int.mul_add]
      omega

/-- The zero-initialized form used by the cumulative discrepancy contract. -/
theorem history_identity_zero
    (D : Int)
    (history : List HistoryContribution) :
    foldHistory D history 0 = historyDeficit D history := by
  simpa using history_identity D history 0

/-- Integer strictness is exactly a one-atom rational discrepancy bound. -/
theorem rational_discrepancy_bound
    (D numerator : Int)
    (hD : 0 < D)
    (hLower : -D < numerator)
    (hUpper : numerator < D) :
    abs ((numerator : ℚ) / (D : ℚ)) < 1 := by
  have hDq : (0 : ℚ) < (D : ℚ) := by
    exact_mod_cast hD
  have hLowerQ : (-D : ℚ) < (numerator : ℚ) := by
    exact_mod_cast hLower
  have hUpperQ : (numerator : ℚ) < (D : ℚ) := by
    exact_mod_cast hUpper
  rw [abs_lt]
  constructor
  · apply (lt_div_iff₀ hDq).2
    linarith
  · apply (div_lt_iff₀ hDq).2
    linarith

def cumulativeActual (D : Int) (history : List HistoryContribution) : ℚ :=
  (actualSum history : ℚ) / (D : ℚ)

def cumulativeIdeal (history : List HistoryContribution) : ℚ :=
  allocationSum history

/-- The rational presentation is the integer history numerator divided by D. -/
theorem cumulative_difference_eq_history_ratio
    (D : Int)
    (history : List HistoryContribution)
    (hD : 0 < D) :
    cumulativeActual D history - cumulativeIdeal history =
      (historyDeficit D history : ℚ) / (D : ℚ) := by
  have hDq : (0 : ℚ) < (D : ℚ) := by
    exact_mod_cast hD
  have hDne : (D : ℚ) ≠ 0 := ne_of_gt hDq
  unfold cumulativeActual cumulativeIdeal historyDeficit
  push_cast
  field_simp [hDne]

/-- A strictly bounded final integer state implies sub-atom cumulative error. -/
theorem cumulative_difference_below_one_atom
    (D : Int)
    (history : List HistoryContribution)
    (hD : 0 < D)
    (hLower : -D < foldHistory D history 0)
    (hUpper : foldHistory D history 0 < D) :
    abs (cumulativeActual D history - cumulativeIdeal history) < 1 := by
  have hIdentity := history_identity_zero D history
  have hNumeratorLower : -D < historyDeficit D history := by
    rw [← hIdentity]
    exact hLower
  have hNumeratorUpper : historyDeficit D history < D := by
    rw [← hIdentity]
    exact hUpper
  rw [cumulative_difference_eq_history_ratio D history hD]
  exact rational_discrepancy_bound D (historyDeficit D history) hD
    hNumeratorLower hNumeratorUpper

/-- Project one B04 occurrence to role 0's actual/allocation history entry. -/
def role0Contribution
    {D : Int}
    (occurrence : AuthenticatedOccurrence D) : HistoryContribution :=
  { actual := occurrence.fraction0
    allocation := occurrence.bonus0 }

def role0Contributions
    {D : Int}
    (segment : List (AuthenticatedOccurrence D)) : List HistoryContribution :=
  segment.map role0Contribution

/-- The role-0 integer fold over one ordered B04 segment. -/
def foldRole0Segment
    (D : Int)
    (segment : List (AuthenticatedOccurrence D))
    (initial : Int) : Int :=
  segment.foldl
    (fun state occurrence =>
      updateDeficit D state occurrence.fraction0 occurrence.bonus0)
    initial

/-- The role-0 integer fold over the nested B04 word, preserving segments. -/
def foldRole0Word
    (D : Int)
    (word : List (List (AuthenticatedOccurrence D)))
    (initial : Int) : Int :=
  word.foldl (fun state segment => foldRole0Segment D segment state) initial

def role0WordHistoryDeficit
    (D : Int)
    (word : List (List (AuthenticatedOccurrence D))) : Int :=
  word.foldl
    (fun numerator segment =>
      numerator + historyDeficit D (role0Contributions segment))
    0

/-- The abstract history identity applies directly to one B04 segment. -/
theorem role0_segment_history_identity
    (D : Int)
    (segment : List (AuthenticatedOccurrence D))
    (initial : Int) :
    foldRole0Segment D segment initial =
      initial + historyDeficit D (role0Contributions segment) := by
  induction segment generalizing initial with
  | nil =>
      simp [foldRole0Segment, role0Contributions, historyDeficit,
        actualSum, allocationSum]
  | cons occurrence rest ih =>
      change foldRole0Segment D rest
          (updateDeficit D initial occurrence.fraction0 occurrence.bonus0) =
        initial + historyDeficit D
          (role0Contribution occurrence :: role0Contributions rest)
      rw [ih]
      simp [historyDeficit, actualSum, allocationSum, role0Contributions,
        role0Contribution, updateDeficit, Int.mul_add]
      omega

/-- The nested B04 word identity preserves segment order and boundaries. -/
private theorem foldl_add_initial
    {α : Type}
    (value : α → Int)
    (values : List α)
    (initial : Int) :
    values.foldl (fun accumulator item => accumulator + value item) initial =
      initial + values.foldl (fun accumulator item => accumulator + value item) 0 := by
  induction values generalizing initial with
  | nil =>
      simp
  | cons valueHead valuesTail ih =>
      simp only [List.foldl]
      rw [ih (initial + value valueHead)]
      simp only [Int.zero_add]
      rw [ih (value valueHead)]
      omega

/-- The nested B04 word identity preserves segment order and boundaries. -/
theorem role0_word_history_identity
    (D : Int)
    (word : List (List (AuthenticatedOccurrence D)))
    (initial : Int) :
    foldRole0Word D word initial =
      initial + role0WordHistoryDeficit D word := by
  induction word generalizing initial with
  | nil =>
      simp [foldRole0Word, role0WordHistoryDeficit]
  | cons segment rest ih =>
      change foldRole0Word D rest (foldRole0Segment D segment initial) =
        initial + role0WordHistoryDeficit D (segment :: rest)
      rw [ih, role0_segment_history_identity]
      have hAdd := foldl_add_initial
        (fun nextSegment : List (AuthenticatedOccurrence D) =>
          historyDeficit D (role0Contributions nextSegment))
        rest
        (historyDeficit D (role0Contributions segment))
      simpa [role0WordHistoryDeficit, Int.add_assoc, Int.add_left_comm,
        Int.add_comm] using hAdd.symm

end FCISFeeApportionmentSRGDCumulative
