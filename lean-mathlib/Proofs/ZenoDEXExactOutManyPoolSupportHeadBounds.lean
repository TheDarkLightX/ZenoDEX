import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Proofs.ZenoDEXExactOutManyPoolSupportTailRecursion

open scoped Classical BigOperators

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolSupportHeadBounds

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolSupportTailRecursion

/-- Sum of audited capacities over the residual support after removing the chosen
head leg. This is the exact support-side overapproximation that the concrete
generator's `future_max` must dominate. -/
def residualSupportCap {n Q : ℕ}
    (cap : Fin n → ℕ)
    (alloc : Alloc n Q)
    (headIdx : Fin n) : ℕ :=
  Finset.sum ((supportSet alloc).erase headIdx) cap

/-- The head leg of a feasible support presentation is bounded below by the
residual support capacities and above by both its own audited capacity and the
remaining exact-out target. -/
theorem feasible_support_cons_head_capacity_bounds
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail) :
    Q - residualSupportCap cap alloc head.1 ≤ head.2 ∧
      head.2 ≤ min (cap head.1) Q := by
  rcases feasible_support_cons_residual_obligations (hFeas := hFeas) (hLegs := hLegs) with
    ⟨_hHeadEq, _hHeadPos, hHeadCap, _hTailSorted, _hTailNodup, _hTailLen,
      hResidual, _hTailGt, _hTailPos, _hTailCap⟩
  have hResidualLeCap :
      Finset.sum ((supportSet alloc).erase head.1) (fun i => (alloc i : ℕ)) ≤
        residualSupportCap cap alloc head.1 := by
    exact Finset.sum_le_sum (fun i _hi => hFeas.1 i)
  have hLower : Q - residualSupportCap cap alloc head.1 ≤ head.2 := by
    omega
  have hHeadLeQ : head.2 ≤ Q := by
    omega
  exact ⟨hLower, le_min hHeadCap hHeadLeQ⟩

/-- If `futureMax` soundly over-approximates the residual support capacities,
then the chosen head leg lies inside the concrete generator's recursive
`amount_out` range for that branch. -/
theorem feasible_support_cons_head_within_future_range
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail)
    {futureMax : ℕ}
    (hFuture : residualSupportCap cap alloc head.1 ≤ futureMax) :
    max 1 (Q - futureMax) ≤ head.2 ∧
      head.2 ≤ min (cap head.1) Q := by
  rcases feasible_support_cons_residual_obligations (hFeas := hFeas) (hLegs := hLegs) with
    ⟨_hHeadEq, hHeadPos, _hHeadCap, _hTailSorted, _hTailNodup, _hTailLen,
      _hResidual, _hTailGt, _hTailPos, _hTailCap⟩
  rcases feasible_support_cons_head_capacity_bounds (hFeas := hFeas) (hLegs := hLegs) with
    ⟨hLowerCap, hUpper⟩
  have hLower : Q - futureMax ≤ head.2 := by
    omega
  exact ⟨max_le_iff.2 ⟨hHeadPos, hLower⟩, hUpper⟩

end ExactOutManyPoolSupportHeadBounds
end ZenoDEX
end TauSwap
