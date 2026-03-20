import Mathlib.Order.Synonym
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Basic
import Proofs.ZenoDEXExactOutCanonicalMinimizer

open scoped Classical

namespace TauSwap
namespace ZenoDEX
namespace ExactOutBruteforceCompleteness

open ExactOutCanonicalMinimizer

/--
Finite-interval search set for exact-out candidate keys.

The intended runtime interpretation is:
- enumerate a bounded interval of candidate splits,
- map each candidate to the full exact-out canonical key
  `(input_total, leg_count, legs_lex)`,
- choose the unique minimum key.
-/
def searchSet {PoolId : Type} [LinearOrder PoolId]
    (routeKey : Nat → Key PoolId) (lo hi : Nat) : Finset (Key PoolId) :=
  (Finset.Icc lo hi).image routeKey

theorem mem_searchSet {PoolId : Type} [LinearOrder PoolId]
    {routeKey : Nat → Key PoolId} {lo hi q0 : Nat}
    (hMem : q0 ∈ Finset.Icc lo hi) :
    routeKey q0 ∈ searchSet routeKey lo hi := by
  exact Finset.mem_image.mpr ⟨q0, hMem, rfl⟩

theorem searchSet_nonempty {PoolId : Type} [LinearOrder PoolId]
    {routeKey : Nat → Key PoolId} {lo hi : Nat} (hRange : lo ≤ hi) :
    (searchSet routeKey lo hi).Nonempty := by
  exact ⟨routeKey lo, mem_searchSet (by simp [hRange])⟩

theorem witness_key_le_all {PoolId : Type} [LinearOrder PoolId]
    {routeKey : Nat → Key PoolId} {lo hi qStar : Nat}
    (hMin : ∀ x ∈ Finset.Icc lo hi, routeKey qStar ≤ routeKey x) :
    ∀ y ∈ searchSet routeKey lo hi, routeKey qStar ≤ y := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  exact hMin x hx

theorem witness_is_canonical {PoolId : Type} [LinearOrder PoolId]
    {routeKey : Nat → Key PoolId} {lo hi qStar : Nat}
    (hRange : qStar ∈ Finset.Icc lo hi)
    (hMin : ∀ x ∈ Finset.Icc lo hi, routeKey qStar ≤ routeKey x) :
    routeKey qStar ∈ searchSet routeKey lo hi ∧
      ∀ y ∈ searchSet routeKey lo hi, routeKey qStar ≤ y := by
  exact ⟨mem_searchSet hRange, witness_key_le_all hMin⟩

theorem witness_eq_searchSet_min {PoolId : Type} [LinearOrder PoolId]
    {routeKey : Nat → Key PoolId} {lo hi qStar : Nat}
    (hRange : qStar ∈ Finset.Icc lo hi)
    (hMin : ∀ x ∈ Finset.Icc lo hi, routeKey qStar ≤ routeKey x) :
    routeKey qStar =
      (searchSet routeKey lo hi).min'
        (searchSet_nonempty
          (routeKey := routeKey)
          (lo := lo)
          (hi := hi)
          (by
            have hBounds := Finset.mem_Icc.mp hRange
            exact Nat.le_trans hBounds.1 hBounds.2)) := by
  have hCanon : routeKey qStar ∈ searchSet routeKey lo hi ∧
      ∀ y ∈ searchSet routeKey lo hi, routeKey qStar ≤ y :=
    witness_is_canonical hRange hMin
  have hS :
      (searchSet routeKey lo hi).Nonempty :=
    searchSet_nonempty
      (routeKey := routeKey)
      (lo := lo)
      (hi := hi)
      (by
        have hBounds := Finset.mem_Icc.mp hRange
        exact Nat.le_trans hBounds.1 hBounds.2)
  have hkMin : routeKey qStar ≤ (searchSet routeKey lo hi).min' hS :=
    hCanon.2 ((searchSet routeKey lo hi).min' hS) (Finset.min'_mem _ _)
  have hMinK : (searchSet routeKey lo hi).min' hS ≤ routeKey qStar :=
    Finset.min'_le _ _ hCanon.1
  exact le_antisymm hkMin hMinK

theorem witness_prefers_fewer_legs_then_lex {PoolId : Type} [LinearOrder PoolId]
    {routeKey : Nat → Key PoolId} {lo hi qStar : Nat}
    (hRange : qStar ∈ Finset.Icc lo hi)
    (hMin : ∀ x ∈ Finset.Icc lo hi, routeKey qStar ≤ routeKey x) :
    routeKey qStar ∈ searchSet routeKey lo hi ∧
      (∀ y ∈ searchSet routeKey lo hi, inputTotal (routeKey qStar) ≤ inputTotal y) ∧
      (∀ y ∈ searchSet routeKey lo hi,
        inputTotal (routeKey qStar) = inputTotal y →
          legCount (routeKey qStar) ≤ legCount y) ∧
      (∀ y ∈ searchSet routeKey lo hi,
        inputTotal (routeKey qStar) = inputTotal y →
          legCount (routeKey qStar) = legCount y →
            legsLex (routeKey qStar) ≤ legsLex y) := by
  let S := searchSet routeKey lo hi
  have hBounds := Finset.mem_Icc.mp hRange
  have hLoHi : lo ≤ hi := Nat.le_trans hBounds.1 hBounds.2
  have hS : S.Nonempty := searchSet_nonempty (routeKey := routeKey) (lo := lo) (hi := hi) hLoHi
  have hkEq : S.min' hS = routeKey qStar := by
    simpa [S] using (witness_eq_searchSet_min (routeKey := routeKey) (lo := lo) (hi := hi) (qStar := qStar) hRange hMin).symm
  simpa [S, hkEq] using canonical_prefers_fewer_legs_then_lex (S := S) hS

theorem witness_is_unique_canonical {PoolId : Type} [LinearOrder PoolId]
    {routeKey : Nat → Key PoolId} {lo hi qStar : Nat}
    (hRange : qStar ∈ Finset.Icc lo hi)
    (hMin : ∀ x ∈ Finset.Icc lo hi, routeKey qStar ≤ routeKey x) :
    ∃! k, k ∈ searchSet routeKey lo hi ∧ ∀ y ∈ searchSet routeKey lo hi, k ≤ y := by
  let S := searchSet routeKey lo hi
  have hCanon : routeKey qStar ∈ S ∧ ∀ y ∈ S, routeKey qStar ≤ y := witness_is_canonical hRange hMin
  have hBounds := Finset.mem_Icc.mp hRange
  have hLoHi : lo ≤ hi := Nat.le_trans hBounds.1 hBounds.2
  have hS : S.Nonempty := searchSet_nonempty (routeKey := routeKey) (lo := lo) (hi := hi) hLoHi
  exact ⟨routeKey qStar, hCanon,
    by
      intro k hk
      have hkEqMin : k = S.min' hS := by
        have hkMin : k ≤ S.min' hS := hk.2 (S.min' hS) (Finset.min'_mem S hS)
        have hMinK : S.min' hS ≤ k := Finset.min'_le S k hk.1
        exact le_antisymm hkMin hMinK
      have hqEqMin : routeKey qStar = S.min' hS := by
        have hqMin : routeKey qStar ≤ S.min' hS := hCanon.2 (S.min' hS) (Finset.min'_mem S hS)
        have hMinQ : S.min' hS ≤ routeKey qStar := Finset.min'_le S (routeKey qStar) hCanon.1
        exact le_antisymm hqMin hMinQ
      exact hkEqMin.trans hqEqMin.symm⟩

end ExactOutBruteforceCompleteness
end ZenoDEX
end TauSwap
