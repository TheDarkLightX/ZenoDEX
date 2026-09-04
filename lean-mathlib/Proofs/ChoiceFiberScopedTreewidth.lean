import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum

/-!
# Scoped choice-fiber minima and exact coverage

This file proves the mathematical core used by the bounded
choice-fiber/treewidth research verifier:

1. substituting fixed Boolean signs into a pseudo-Boolean polynomial preserves
   evaluation;
2. an exact pair of Boolean fiber messages yields the exact minimum after one
   elimination step;
3. exact cell minima aggregate to the minimum of an exact partition; and
4. exact scoped minima and exact coverage compose to the minimum over the
   declared whole set.

The theorems do not establish the Python decomposition algorithm, canonical
encoding or roots, source binding, a Python/Rust refinement, RISC0 receipt
soundness, a ZRPF guest, M6 closure, or settlement authority.

They also do not establish canonical argmin tie-breaking, induced-width
correctness, separator or factor ownership, resource-preflight bounds, or the
Python-bitmask-to-Lean-scope projection. Tree-decomposition validity, the
running-intersection property, local-factor plus child-message decomposition,
and runtime message-table verification remain separate refinement obligations.
-/

open scoped BigOperators

namespace ZenoDEX.NamedChoiceFiberTreewidth

abbrev Assignment (n : Nat) := Fin n → Bool

abbrev Scope (n : Nat) := Fin n → Option Bool

/-- The pseudo-Boolean sign represented by one Boolean choice. -/
def sign : Bool → Int
  | false => -1
  | true => 1

/-- Replace every coordinate fixed by `q`, retaining `x` elsewhere. -/
def complete {n : Nat} (q : Scope n) (x : Assignment n) : Assignment n :=
  fun i => (q i).getD (x i)

/-- A complete assignment agrees with every coordinate fixed by the scope. -/
def Extends {n : Nat} (q : Scope n) (x : Assignment n) : Prop :=
  ∀ i b, q i = some b → x i = b

/-- The subcube of complete assignments admitted by a scope. -/
def scopeSet {n : Nat} (q : Scope n) : Set (Assignment n) :=
  {x | Extends q x}

/-- One multilinear pseudo-Boolean monomial. -/
structure Term (n : Nat) where
  coefficient : Int
  support : Finset (Fin n)
  deriving DecidableEq

/-- A polynomial is a finite ordered source-term list. -/
abbrev Polynomial (n : Nat) := List (Term n)

def evalTerm {n : Nat} (t : Term n) (x : Assignment n) : Int :=
  t.coefficient * t.support.prod (fun i => sign (x i))

def evalPolynomial {n : Nat} (p : Polynomial n) (x : Assignment n) : Int :=
  (p.map fun t => evalTerm t x).sum

def fixedSupport {n : Nat} (q : Scope n) (s : Finset (Fin n)) : Finset (Fin n) :=
  s.filter fun i => (q i).isSome

def freeSupport {n : Nat} (q : Scope n) (s : Finset (Fin n)) : Finset (Fin n) :=
  s.filter fun i => ¬(q i).isSome

/-- Absorb fixed signs into the coefficient and retain the free support. -/
def restrictTerm {n : Nat} (q : Scope n) (t : Term n) : Term n :=
  {
    coefficient :=
      t.coefficient *
        (fixedSupport q t.support).prod (fun i => sign ((q i).getD false))
    support := freeSupport q t.support
  }

def restrictPolynomial {n : Nat} (q : Scope n) (p : Polynomial n) : Polynomial n :=
  p.map (restrictTerm q)

/-- `minimum` is attained on `s` and is a lower bound for every value on `s`. -/
def IsMinimumOn {α : Type} (f : α → Int) (s : Set α) (minimum : Int) : Prop :=
  (∃ x, x ∈ s ∧ f x = minimum) ∧ ∀ x, x ∈ s → minimum ≤ f x

private theorem eval_restrictTerm {n : Nat} (q : Scope n) (t : Term n)
    (x : Assignment n) :
    evalTerm (restrictTerm q t) x = evalTerm t (complete q x) := by
  classical
  have hFixed :
      (fixedSupport q t.support).prod (fun i => sign ((q i).getD false)) =
        (fixedSupport q t.support).prod (fun i => sign (complete q x i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨_, hiSome⟩
    cases hqi : q i with
    | none => simp [hqi] at hiSome
    | some b => simp [complete, hqi]
  have hFree :
      (freeSupport q t.support).prod (fun i => sign (x i)) =
        (freeSupport q t.support).prod (fun i => sign (complete q x i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨_, hiNone⟩
    cases hqi : q i with
    | none => simp [complete, hqi]
    | some b => simp [hqi] at hiNone
  rw [evalTerm, restrictTerm, evalTerm, hFixed, hFree]
  simp only [fixedSupport, freeSupport]
  rw [mul_assoc, Finset.prod_filter_mul_prod_filter_not]

/-- Substitution of fixed scope signs preserves polynomial evaluation exactly. -/
theorem scope_substitution_correct {n : Nat} (q : Scope n) (p : Polynomial n)
    (x : Assignment n) :
    evalPolynomial (restrictPolynomial q p) x = evalPolynomial p (complete q x) := by
  unfold evalPolynomial restrictPolynomial
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  exact eval_restrictTerm q t x

/-- Completing an arbitrary assignment always produces a member of the scope. -/
theorem complete_extends {n : Nat} (q : Scope n) (x : Assignment n) :
    Extends q (complete q x) := by
  intro i b hib
  simp [complete, hib]

/-- Completion is the identity on assignments already satisfying the scope. -/
theorem complete_eq_of_extends {n : Nat} {q : Scope n} {x : Assignment n}
    (hx : Extends q x) : complete q x = x := by
  funext i
  cases hqi : q i with
  | none => simp [complete, hqi]
  | some b => simpa [complete, hqi] using (hx i b hqi).symm

/--
An exact minimum of the restricted polynomial is exactly an original-polynomial
minimum over the assignments satisfying the scope.
-/
theorem restricted_minimum_iff {n : Nat} (q : Scope n) (p : Polynomial n)
    (minimum : Int) :
    IsMinimumOn (evalPolynomial (restrictPolynomial q p)) Set.univ minimum ↔
      IsMinimumOn (evalPolynomial p) (scopeSet q) minimum := by
  constructor
  · intro hRestricted
    rcases hRestricted.1 with ⟨x, _, hxValue⟩
    constructor
    · have hCompletedValue : evalPolynomial p (complete q x) = minimum := by
        simpa [scope_substitution_correct] using hxValue
      exact ⟨complete q x, complete_extends q x, hCompletedValue⟩
    · intro y hy
      have hyComplete : complete q y = y := complete_eq_of_extends hy
      have hLower := hRestricted.2 y (Set.mem_univ y)
      rw [scope_substitution_correct, hyComplete] at hLower
      exact hLower
  · intro hScoped
    rcases hScoped.1 with ⟨x, hxScope, hxValue⟩
    constructor
    · have hxComplete : complete q x = x := complete_eq_of_extends hxScope
      have hRestrictedValue :
          evalPolynomial (restrictPolynomial q p) x = minimum := by
        rw [scope_substitution_correct, hxComplete]
        exact hxValue
      exact ⟨x, Set.mem_univ x, hRestrictedValue⟩
    · intro y _
      have hLower := hScoped.2 (complete q y) (complete_extends q y)
      rwa [← scope_substitution_correct] at hLower

/-- One Boolean fiber of a conditional minimization problem. -/
def boolFiber {α : Type} (domain : Set α) (introduced : α → Bool)
    (signValue : Bool) : Set α :=
  {x | x ∈ domain ∧ introduced x = signValue}

/-- The message sent after eliminating one Boolean choice. -/
def eliminationMessage (negative positive : Int) : Int :=
  min negative positive

/--
One exact Boolean elimination step. In the treewidth instantiation, `domain` is
the set of subtree assignments compatible with a separator assignment, and
`introduced` reads the bag variable being eliminated. The branch costs may
already include owned factors and exact child messages. Each branch must be
nonempty, as witnessed by `IsMinimumOn`; this matches the unconstrained Boolean
cube admitted by the reference verifier.
-/
theorem eliminationMessage_correct {α : Type} (f : α → Int) (domain : Set α)
    (introduced : α → Bool) (negative positive : Int)
    (hNegative : IsMinimumOn f (boolFiber domain introduced false) negative)
    (hPositive : IsMinimumOn f (boolFiber domain introduced true) positive) :
    IsMinimumOn f domain (eliminationMessage negative positive) := by
  constructor
  · by_cases hle : negative ≤ positive
    · rcases hNegative.1 with ⟨x, hx, hxValue⟩
      have hxMinimum : f x = eliminationMessage negative positive := by
        calc
          f x = negative := hxValue
          _ = eliminationMessage negative positive := (min_eq_left hle).symm
      exact ⟨x, hx.1, hxMinimum⟩
    · rcases hPositive.1 with ⟨x, hx, hxValue⟩
      have hle' : positive ≤ negative := le_of_not_ge hle
      have hxMinimum : f x = eliminationMessage negative positive := by
        calc
          f x = positive := hxValue
          _ = eliminationMessage negative positive := (min_eq_right hle').symm
      exact ⟨x, hx.1, hxMinimum⟩
  · intro x hxDomain
    cases hSign : introduced x with
    | false =>
        exact
          le_trans (min_le_left negative positive)
            (hNegative.2 x ⟨hxDomain, hSign⟩)
    | true =>
        exact
          le_trans (min_le_right negative positive)
            (hPositive.2 x ⟨hxDomain, hSign⟩)

/--
An abstract bottom-up message tree. Leaves carry exact fully reduced costs;
each internal node eliminates one Boolean choice by taking the minimum of its
two exact child messages.
-/
inductive ExactMessageRecurrence {α : Type} (f : α → Int) : Set α → Int → Prop where
  | leaf {domain minimum} :
      IsMinimumOn f domain minimum → ExactMessageRecurrence f domain minimum
  | eliminate {domain negative positive} (introduced : α → Bool) :
      ExactMessageRecurrence f (boolFiber domain introduced false) negative →
      ExactMessageRecurrence f (boolFiber domain introduced true) positive →
      ExactMessageRecurrence f domain (eliminationMessage negative positive)

/-- Every finite tree of exact Boolean message steps returns its exact root minimum. -/
theorem ExactMessageRecurrence.sound {α : Type} {f : α → Int} {domain : Set α}
    {minimum : Int} (h : ExactMessageRecurrence f domain minimum) :
    IsMinimumOn f domain minimum := by
  induction h with
  | leaf hExact => exact hExact
  | @eliminate domain negative positive introduced _ _ hNegative hPositive =>
      exact
        eliminationMessage_correct f domain introduced negative positive hNegative hPositive

/-- A family of cells covers the universe and assigns every element to one cell. -/
def ExactPartition {Ω ι : Type} (whole : Set Ω) (cells : ι → Set Ω) : Prop :=
  (∀ x, x ∈ whole ↔ ∃ i, x ∈ cells i) ∧
    ∀ i j x, x ∈ cells i → x ∈ cells j → i = j

/--
Exact cell minima aggregate to the universe minimum. Disjointness is retained
in `ExactPartition` because the coverage certificate requires unique leaf
ownership, although minimum equality itself needs only complete coverage.
-/
theorem exactPartition_minimum_iff {Ω ι : Type} (whole : Set Ω)
    (cells : ι → Set Ω) (f : Ω → Int) (cellMinimum : ι → Int) (minimum : Int)
    (hPartition : ExactPartition whole cells)
    (hCells : ∀ i, IsMinimumOn f (cells i) (cellMinimum i)) :
    IsMinimumOn f whole minimum ↔
      IsMinimumOn cellMinimum Set.univ minimum := by
  constructor
  · intro hGlobal
    rcases hGlobal.1 with ⟨x, hxUniverse, hxValue⟩
    rcases (hPartition.1 x).mp hxUniverse with ⟨i, hxCell⟩
    rcases (hCells i).1 with ⟨y, hyCell, hyValue⟩
    have hyWhole : y ∈ whole := (hPartition.1 y).mpr ⟨i, hyCell⟩
    have hCellLe : cellMinimum i ≤ minimum := by
      rw [← hxValue]
      exact (hCells i).2 x hxCell
    have hGlobalLe : minimum ≤ cellMinimum i := by
      rw [← hyValue]
      exact hGlobal.2 y hyWhole
    constructor
    · exact ⟨i, Set.mem_univ i, le_antisymm hCellLe hGlobalLe⟩
    · intro j _
      rcases (hCells j).1 with ⟨z, hzCell, hzValue⟩
      have hzWhole : z ∈ whole := (hPartition.1 z).mpr ⟨j, hzCell⟩
      rw [← hzValue]
      exact hGlobal.2 z hzWhole
  · intro hAggregate
    rcases hAggregate.1 with ⟨i, _, hiValue⟩
    rcases (hCells i).1 with ⟨x, hxCell, hxValue⟩
    constructor
    · have hxMinimum : f x = minimum := by
        calc
          f x = cellMinimum i := hxValue
          _ = minimum := hiValue
      exact ⟨x, (hPartition.1 x).mpr ⟨i, hxCell⟩, hxMinimum⟩
    · intro y hyUniverse
      rcases (hPartition.1 y).mp hyUniverse with ⟨j, hyCell⟩
      exact le_trans (hAggregate.2 j (Set.mem_univ j)) ((hCells j).2 y hyCell)

/--
Exact scoped elimination minima plus exact scope coverage imply the exact
minimum of the original polynomial over `whole`.
-/
theorem scoped_treewidth_partition_composition {n : Nat} {ι : Type}
    (p : Polynomial n) (scopes : ι → Scope n) (whole : Set (Assignment n))
    (cellMinimum : ι → Int) (minimum : Int)
    (hPartition : ExactPartition whole (fun i => scopeSet (scopes i)))
    (hMessages :
      ∀ i,
        ExactMessageRecurrence
          (evalPolynomial (restrictPolynomial (scopes i) p)) Set.univ
          (cellMinimum i))
    (hAggregate : IsMinimumOn cellMinimum Set.univ minimum) :
    IsMinimumOn (evalPolynomial p) whole minimum := by
  have hScoped :
      ∀ i, IsMinimumOn (evalPolynomial p) (scopeSet (scopes i)) (cellMinimum i) := by
    intro i
    exact
      (restricted_minimum_iff (q := scopes i) (p := p)
        (minimum := cellMinimum i)).mp (hMessages i).sound
  exact
    (exactPartition_minimum_iff (whole := whole)
      (cells := fun i => scopeSet (scopes i)) (f := evalPolynomial p)
      (cellMinimum := cellMinimum) (minimum := minimum) hPartition hScoped).mpr
      hAggregate

/-! ## Non-vacuity and the separator counterexample -/

private def singletonTerm (i : Fin 2) : Term 2 :=
  ⟨1, {i}⟩

private def pairTerm : Term 2 :=
  ⟨1, {0, 1}⟩

/-- `f(y,z) = y + z + yz`. -/
def separatorCounterexample : Polynomial 2 :=
  [singletonTerm 0, singletonTerm 1, pairTerm]

/-- The first owner bag in the separator counterexample. -/
def firstOwnerBag : Polynomial 2 :=
  [singletonTerm 0]

/-- The second, overlapping owner bag in the separator counterexample. -/
def secondOwnerBag : Polynomial 2 :=
  [singletonTerm 1, pairTerm]

/-- The true minimum of `y + z + yz` is `-1`. -/
theorem separatorCounterexample_exact_minimum :
    IsMinimumOn (evalPolynomial separatorCounterexample) Set.univ (-1) := by
  constructor
  · let x : Assignment 2 := fun _ => false
    have hxValue : evalPolynomial separatorCounterexample x = -1 := by
      norm_num [x, separatorCounterexample, singletonTerm, pairTerm, evalPolynomial,
        evalTerm, sign]
    exact ⟨x, Set.mem_univ x, hxValue⟩
  · intro x _
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      norm_num [separatorCounterexample, singletonTerm, pairTerm, evalPolynomial, evalTerm,
        sign, h0, h1]

/-- Independent minimization of the two overlapping owner bags reports `-3`. -/
theorem independent_owner_bag_minima_report_minus_three :
    IsMinimumOn (evalPolynomial firstOwnerBag) Set.univ (-1) ∧
      IsMinimumOn (evalPolynomial secondOwnerBag) Set.univ (-2) ∧
        (-1 : Int) + (-2 : Int) = -3 := by
  constructor
  · constructor
    · let x : Assignment 2 := fun _ => false
      have hxValue : evalPolynomial firstOwnerBag x = -1 := by
        norm_num [x, firstOwnerBag, singletonTerm, evalPolynomial, evalTerm, sign]
      exact ⟨x, Set.mem_univ x, hxValue⟩
    · intro x _
      cases h0 : x 0 <;>
        norm_num [firstOwnerBag, singletonTerm, evalPolynomial, evalTerm, sign, h0]
  · constructor
    · constructor
      · let x : Assignment 2 := fun i => if i = 0 then true else false
        have hxValue : evalPolynomial secondOwnerBag x = -2 := by
          norm_num [x, secondOwnerBag, singletonTerm, pairTerm, evalPolynomial, evalTerm,
            sign]
        exact ⟨x, Set.mem_univ x, hxValue⟩
      · intro x _
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          norm_num [secondOwnerBag, singletonTerm, pairTerm, evalPolynomial, evalTerm,
            sign, h0, h1]
    · norm_num

/-- The `-3` obtained from independent overlapping-bag minima is unattainable. -/
theorem independent_owner_bag_value_is_unattainable :
    ¬∃ x, evalPolynomial separatorCounterexample x = -3 := by
  intro h
  rcases h with ⟨x, hxValue⟩
  have hLower := separatorCounterexample_exact_minimum.2 x (Set.mem_univ x)
  rw [hxValue] at hLower
  norm_num at hLower

end ZenoDEX.NamedChoiceFiberTreewidth
