import Proofs.ChoiceFiberScopedTreewidth

/-!
# Exact theorem-shape challenge for scoped choice-fiber minima

This module pins the substantive theorem types consumed by the research claim.
A renamed theorem with a weakened conclusion, including `True`, cannot satisfy
these checks.
-/

namespace ZenoDEX.NamedChoiceFiberTreewidth

#check (scope_substitution_correct :
  ∀ {n : Nat} (q : Scope n) (p : Polynomial n) (x : Assignment n),
    evalPolynomial (restrictPolynomial q p) x = evalPolynomial p (complete q x))

#check (restricted_minimum_iff :
  ∀ {n : Nat} (q : Scope n) (p : Polynomial n) (minimum : Int),
    IsMinimumOn (evalPolynomial (restrictPolynomial q p)) Set.univ minimum ↔
      IsMinimumOn (evalPolynomial p) (scopeSet q) minimum)

#check (ExactMessageRecurrence.sound :
  ∀ {α : Type} {f : α → Int} {domain : Set α} {minimum : Int},
    ExactMessageRecurrence f domain minimum → IsMinimumOn f domain minimum)

#check (exactPartition_minimum_iff :
  ∀ {Ω ι : Type} (whole : Set Ω) (cells : ι → Set Ω) (f : Ω → Int)
      (cellMinimum : ι → Int) (minimum : Int),
    ExactPartition whole cells →
      (∀ i, IsMinimumOn f (cells i) (cellMinimum i)) →
      (IsMinimumOn f whole minimum ↔ IsMinimumOn cellMinimum Set.univ minimum))

#check (scoped_treewidth_partition_composition :
  ∀ {n : Nat} {ι : Type} (p : Polynomial n) (scopes : ι → Scope n)
      (whole : Set (Assignment n)) (cellMinimum : ι → Int) (minimum : Int),
    ExactPartition whole (fun i => scopeSet (scopes i)) →
      (∀ i,
        ExactMessageRecurrence
          (evalPolynomial (restrictPolynomial (scopes i) p)) Set.univ
          (cellMinimum i)) →
      IsMinimumOn cellMinimum Set.univ minimum →
      IsMinimumOn (evalPolynomial p) whole minimum)

#check (separatorCounterexample_exact_minimum :
  IsMinimumOn (evalPolynomial separatorCounterexample) Set.univ (-1))

#check (independent_owner_bag_minima_report_minus_three :
  IsMinimumOn (evalPolynomial firstOwnerBag) Set.univ (-1) ∧
    IsMinimumOn (evalPolynomial secondOwnerBag) Set.univ (-2) ∧
      (-1 : Int) + (-2 : Int) = -3)

#check (independent_owner_bag_value_is_unattainable :
  ¬∃ x, evalPolynomial separatorCounterexample x = -3)

/-!
The checker output for these commands is consumed by the focused gate. Standard
Lean quotient and extensionality axioms are permitted; `sorryAx` is not.
-/

#print axioms scope_substitution_correct
#print axioms restricted_minimum_iff
#print axioms ExactMessageRecurrence.sound
#print axioms exactPartition_minimum_iff
#print axioms scoped_treewidth_partition_composition
#print axioms separatorCounterexample_exact_minimum
#print axioms independent_owner_bag_minima_report_minus_three
#print axioms independent_owner_bag_value_is_unattainable

end ZenoDEX.NamedChoiceFiberTreewidth
