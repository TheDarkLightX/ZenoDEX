import Proofs.FCISFeeApportionmentSRGD

namespace FCISFeeOccurrenceSemantics

open FCISFeeApportionmentSRGD

/-- Forget the exact witness decomposition but retain one segment's amount. -/
def segmentMass (witnessAmounts : List Nat) : Nat :=
  witnessAmounts.sum

/-- Retain accepted-transition boundaries as an ordered word of segment masses. -/
def segmentMasses (history : List (List Nat)) : List Nat :=
  history.map segmentMass

/-- Same-transition split/merge is a non-injective semantic projection. -/
theorem witness_projection_noninjective :
    segmentMass [867] = segmentMass [493, 374] ∧
      [867] ≠ [493, 374] := by
  decide

/-- Equal global mass does not determine the accepted-transition word. -/
theorem global_mass_forgets_transition_boundaries :
    segmentMass (List.flatten [[493, 374]]) =
        segmentMass (List.flatten [[493], [374]]) ∧
      segmentMasses [[493, 374]] ≠ segmentMasses [[493], [374]] := by
  decide

/-- Update exactly one entitlement key in a product state. -/
def updateAt
    {Key Value : Type}
    [DecidableEq Key]
    (key : Key)
    (update : Value → Value)
    (state : Key → Value) : Key → Value :=
  fun query => if query = key then update (state query) else state query

/--
Distinct-key transitions agree at every observation point, validating canonical
key order per segment without requiring function extensionality.
-/
theorem distinct_key_updates_commute
    {Key Value : Type}
    [DecidableEq Key]
    (left right : Key)
    (leftUpdate rightUpdate : Value → Value)
    (state : Key → Value)
    (query : Key)
    (distinct : left ≠ right) :
    updateAt right rightUpdate (updateAt left leftUpdate state) query =
      updateAt left leftUpdate (updateAt right rightUpdate state) query := by
  by_cases atLeft : query = left
  · subst query
    simp [updateAt, distinct, Ne.symm distinct]
  · by_cases atRight : query = right
    · subst query
      simp [updateAt, distinct, Ne.symm distinct]
    · simp [updateAt, atLeft, atRight]

/-- A one-step interpretation square lifts through the complete occurrence fold. -/
theorem occurrence_fold_conjugacy
    {Source Target Input : Type}
    (sourceStep : Source → Input → Source)
    (targetStep : Target → Input → Target)
    (interpret : Source → Target)
    (oneStep : ∀ state input,
      targetStep (interpret state) input = interpret (sourceStep state input))
    (inputs : List Input)
    (initial : Source) :
    inputs.foldl targetStep (interpret initial) =
      interpret (inputs.foldl sourceStep initial) := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input rest inductionHypothesis =>
      simp only [List.foldl]
      rw [oneStep initial input]
      exact inductionHypothesis (sourceStep initial input)

/-- Direct amount 3 under the production 25/25/50 policy selects roles 0 and 1. -/
theorem production_whole_bonus :
    SRGDBonusRel 10000 0 0 0 7500 7500 5000 1 1 0 := by
  simp [SRGDBonusRel, IsBonusBit]
  omega

/-- The first split occurrence, amount 1, selects role 2. -/
theorem production_first_split_bonus :
    SRGDBonusRel 10000 0 0 0 2500 2500 5000 0 0 1 := by
  simp [SRGDBonusRel, IsBonusBit]
  omega

/-- After the first split state, amount 2 selects role 0 by fixed tie order. -/
theorem production_second_split_bonus :
    SRGDBonusRel 10000 2500 2500 (-5000) 5000 5000 0 1 0 0 := by
  simp [SRGDBonusRel, IsBonusBit]
  omega

/--
A zero-history production-denominator counterexample: amount 3 is not equivalent
to accepted occurrences 1 then 2. The total allocation and post-state both
change, so cross-boundary merge is not a sound quotient.
-/
theorem production_split_merge_boundary_counterexample :
    (3 : Int) = 1 + 2 ∧
      ((1, 1, 1) : Int × Int × Int) ≠ (1, 0, 2) ∧
      ((-2500, -2500, 5000) : Int × Int × Int) ≠
        (-2500, 7500, -5000) := by
  decide

#print axioms witness_projection_noninjective
#print axioms global_mass_forgets_transition_boundaries
#print axioms distinct_key_updates_commute
#print axioms occurrence_fold_conjugacy
#print axioms production_whole_bonus
#print axioms production_first_split_bonus
#print axioms production_second_split_bonus
#print axioms production_split_merge_boundary_counterexample

end FCISFeeOccurrenceSemantics
