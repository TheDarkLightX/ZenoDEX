import Proofs.ZenoDEXExactOutManyPoolQuotedStructuralReachability
import Proofs.ZenoDEXExactOutManyPoolSupportTailRecursion

open scoped Classical BigOperators

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolQuotedPathRealization

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolSupportTailRecursion
open ExactOutManyPoolStructuralRecursionReachability
open ExactOutManyPoolQuotedStructuralReachability

/-!
# Exact-Out Many-Pool Quoted Path Realization

This file strengthens the selected-domain completeness frontier by proving that a
canonical ordered support presentation already determines a concrete bounded
allocation witness.

The main result is still intentionally local:

- if a support list is sorted by pool index, positive, capacity-bounded, and
  sums to the target `Q`,
- then it can be realized as a bounded allocation with exactly that
  `supportLegs` presentation.

Using the already-checked quoted structural reachability theorem, this upgrades
ordered quoted paths into genuine feasible audited allocations. That removes one
more layer of witness boilerplate from the emitted-stream frontier.
-/

/-- The all-zero bounded allocation for target `0`. -/
def zeroAlloc {n : ℕ} : Alloc n 0 := fun _ => 0

theorem supportSet_zeroAlloc {n : ℕ} :
    supportSet (zeroAlloc (n := n)) = ∅ := by
  ext i
  simp [supportSet, zeroAlloc]

theorem supportLegs_zeroAlloc {n : ℕ} :
    supportLegs (zeroAlloc (n := n)) = [] := by
  simp [supportLegs, supportIndices, supportSet_zeroAlloc, zeroAlloc]

/-- Widen an allocation into a larger ambient target bound without changing any
component values. -/
def widenAlloc {n target Q : ℕ}
    (hTarget : target ≤ Q)
    (alloc : Alloc n target) : Alloc n Q :=
  fun i => ⟨(alloc i : ℕ), Nat.lt_succ_iff.mpr (le_trans (Nat.lt_succ_iff.mp (alloc i).is_lt) hTarget)⟩

@[simp] theorem widenAlloc_val
    {n target Q : ℕ}
    {hTarget : target ≤ Q}
    {alloc : Alloc n target}
    {i : Fin n} :
    ((widenAlloc hTarget alloc i : Fin (Q + 1)) : ℕ) = (alloc i : ℕ) := by
  rfl

theorem supportSet_widenAlloc_eq
    {n target Q : ℕ}
    {hTarget : target ≤ Q}
    {alloc : Alloc n target} :
    supportSet (widenAlloc hTarget alloc) = supportSet alloc := by
  ext i
  simp [supportSet, widenAlloc]

theorem supportIndices_widenAlloc_eq
    {n target Q : ℕ}
    {hTarget : target ≤ Q}
    {alloc : Alloc n target} :
    supportIndices (widenAlloc hTarget alloc) = supportIndices alloc := by
  simp [supportIndices, supportSet_widenAlloc_eq]

theorem supportLegs_widenAlloc_eq
    {n target Q : ℕ}
    {hTarget : target ≤ Q}
    {alloc : Alloc n target} :
    supportLegs (widenAlloc hTarget alloc) = supportLegs alloc := by
  simp [supportLegs, supportIndices_widenAlloc_eq]

theorem map_fst_to_legs_eq_of_vals
    {n : ℕ}
    {legs : List (Fin n × ℕ)}
    {f : Fin n → ℕ}
    (hVals : ∀ leg ∈ legs, f leg.1 = leg.2) :
    (legs.map Prod.fst).map (fun i => (i, f i)) = legs := by
  induction legs with
  | nil =>
      rfl
  | cons leg tail ih =>
      have hHead : f leg.1 = leg.2 := hVals leg (by simp)
      have hTail : ∀ leg' ∈ tail, f leg'.1 = leg'.2 := by
        intro leg' hMem
        exact hVals leg' (by simp [hMem])
      simp [hHead, ih hTail]

theorem supportSet_update_eq_insert
    {n Q : ℕ}
    (alloc : Alloc n Q)
    (idx : Fin n)
    (v : Fin (Q + 1))
    (hFresh : idx ∉ supportSet alloc)
    (hPos : 0 < (v : ℕ)) :
    supportSet (Function.update alloc idx v) = insert idx (supportSet alloc) := by
  ext j
  by_cases hEq : j = idx
  · subst hEq
    constructor
    · intro _
      simp
    · intro _
      exact (mem_supportSet_iff).2 (by simpa [Function.update] using hPos)
  · simp [supportSet, Function.update, hEq]

/-- Canonical ordered support presentations realize concrete bounded
allocations. -/
theorem exists_alloc_of_sorted_support_presentation
    {n Q : ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (legs : List (Fin n × ℕ))
    (hSorted : (legs.map Prod.fst).SortedLT)
    (hLen : legs.length ≤ maxLegs)
    (hSum : (legs.map Prod.snd).sum = Q)
    (hPos : ∀ leg ∈ legs, 0 < leg.2)
    (hCap : ∀ leg ∈ legs, leg.2 ≤ cap leg.1) :
    ∃ alloc : Alloc n Q, Feasible cap maxLegs alloc ∧ supportLegs alloc = legs := by
  induction legs generalizing Q with
  | nil =>
      have hQ : Q = 0 := by
        simpa using hSum.symm
      subst hQ
      exact ⟨
        zeroAlloc (n := n),
        by
          constructor
          · intro i
            simp [zeroAlloc]
          · constructor
            · simp [zeroAlloc]
            · have hZeroLen : (supportLegs (zeroAlloc (n := n))).length ≤ maxLegs := by
                simpa [supportLegs_zeroAlloc] using hLen
              simpa [supportLegs_length] using hZeroLen,
        supportLegs_zeroAlloc (n := n)
      ⟩
  | cons head tail ih =>
      have hTailSorted : (tail.map Prod.fst).SortedLT := by
        simpa using tail_sortedLT_of_cons_sortedLT hSorted
      have hHeadLt : ∀ leg ∈ tail, head.1 < leg.1 := by
        intro leg hMem
        have hMemFst : leg.1 ∈ tail.map Prod.fst := by
          exact List.mem_map.2 ⟨leg, hMem, by simp⟩
        exact head_lt_of_mem_tail_of_cons_sortedLT hSorted hMemFst
      have hHeadPos : 0 < head.2 := hPos head (by simp)
      have hHeadCap : head.2 ≤ cap head.1 := hCap head (by simp)
      have hTailLen : tail.length ≤ maxLegs := by
        exact Nat.le_trans (Nat.le_succ _) hLen
      have hHeadLeQ : head.2 ≤ Q := by
        have hSum' : head.2 + (tail.map Prod.snd).sum = Q := by
          simpa using hSum
        omega
      have hTailSum : (tail.map Prod.snd).sum = Q - head.2 := by
        have hSum' : head.2 + (tail.map Prod.snd).sum = Q := by
          simpa using hSum
        omega
      have hTailPos : ∀ leg ∈ tail, 0 < leg.2 := by
        intro leg hMem
        exact hPos leg (by simp [hMem])
      have hTailCap : ∀ leg ∈ tail, leg.2 ≤ cap leg.1 := by
        intro leg hMem
        exact hCap leg (by simp [hMem])
      rcases ih
          (Q := Q - head.2)
          hTailSorted
          hTailLen
          hTailSum
          hTailPos
          hTailCap with
        ⟨residual, hResidualFeas, hResidualLegs⟩
      let residualW : Alloc n Q := widenAlloc (by omega) residual
      have hResidualWLegs : supportLegs residualW = tail := by
        calc
          supportLegs residualW = supportLegs residual := by
            simpa [residualW] using
              (supportLegs_widenAlloc_eq (hTarget := by omega) (alloc := residual))
          _ = tail := hResidualLegs
      have hResidualCap : ∀ i, (residualW i : ℕ) ≤ cap i := by
        intro i
        exact hResidualFeas.1 i
      have hResidualSum : ∑ i, (residualW i : ℕ) = Q - head.2 := by
        simpa [residualW, widenAlloc] using hResidualFeas.2.1
      have hResidualIndices : supportIndices residualW = tail.map Prod.fst := by
        calc
          supportIndices residualW = (supportLegs residualW).map Prod.fst := by
            simpa using (supportLegs_fst residualW).symm
          _ = tail.map Prod.fst := by
            simpa [hResidualWLegs]
      have hHeadNotMemTail : head.1 ∉ tail.map Prod.fst := by
        intro hMem
        rcases List.mem_map.mp hMem with ⟨leg, hLegMem, hEq⟩
        have hLt : head.1 < leg.1 := hHeadLt leg hLegMem
        rw [hEq] at hLt
        exact lt_irrefl _ hLt
      have hHeadFresh : head.1 ∉ supportSet residualW := by
        intro hMem
        have hPos' : 0 < (residualW head.1 : ℕ) := (mem_supportSet_iff).1 hMem
        have hMemIdx : head.1 ∈ supportIndices residualW := (mem_supportIndices_iff).2 hPos'
        rw [hResidualIndices] at hMemIdx
        exact hHeadNotMemTail hMemIdx
      have hHeadLeast : ∀ b ∈ supportSet residualW, head.1 ≤ b := by
        intro b hb
        have hPos' : 0 < (residualW b : ℕ) := (mem_supportSet_iff).1 hb
        have hMemIdx : b ∈ tail.map Prod.fst := by
          rw [← hResidualIndices]
          exact (mem_supportIndices_iff).2 hPos'
        rcases List.mem_map.mp hMemIdx with ⟨leg, hLegMem, hEq⟩
        rw [← hEq]
        exact le_of_lt (hHeadLt leg hLegMem)
      let headVal : Fin (Q + 1) := ⟨head.2, Nat.lt_succ_iff.mpr hHeadLeQ⟩
      let alloc : Alloc n Q := Function.update residualW head.1 headVal
      have hAllocHead : (alloc head.1 : ℕ) = head.2 := by
        simp [alloc, headVal, Function.update]
      have hTailVals : ∀ leg ∈ tail, (residualW leg.1 : ℕ) = leg.2 := by
        intro leg hMem
        have hMemAll : leg ∈ supportLegs residualW := by
          rw [hResidualWLegs]
          exact hMem
        exact (supportLeg_mem_iff.1 hMemAll).1.symm
      have hTailValsAlloc : ∀ leg ∈ tail, (alloc leg.1 : ℕ) = leg.2 := by
        intro leg hMem
        have hNe : leg.1 ≠ head.1 := by
          have hLt := hHeadLt leg hMem
          omega
        calc
          (alloc leg.1 : ℕ) = (residualW leg.1 : ℕ) := by
            simp [alloc, headVal, Function.update, hNe]
          _ = leg.2 := hTailVals leg hMem
      have hTailMapEq :
          (tail.map Prod.fst).map (fun i => (i, (alloc i : ℕ))) = tail :=
        map_fst_to_legs_eq_of_vals hTailValsAlloc
      have hSupportIndicesAlloc :
          supportIndices alloc = head.1 :: tail.map Prod.fst := by
        have hSet :
            supportSet alloc = insert head.1 (supportSet residualW) :=
          supportSet_update_eq_insert residualW head.1 headVal hHeadFresh (by simpa [headVal])
        calc
          supportIndices alloc = (insert head.1 (supportSet residualW)).sort := by
            simpa [supportIndices, hSet]
          _ = head.1 :: (supportSet residualW).sort := by
            exact Finset.sort_insert (r := fun a b : Fin n => a ≤ b) hHeadLeast hHeadFresh
          _ = head.1 :: tail.map Prod.fst := by
            simpa [supportIndices] using hResidualIndices
      have hSupportLegsAlloc : supportLegs alloc = head :: tail := by
        rw [supportLegs, hSupportIndicesAlloc, List.map_cons]
        simp [hAllocHead, hTailMapEq]
      have hAllocFeasible : Feasible cap maxLegs alloc := by
        constructor
        · intro i
          by_cases hEq : i = head.1
          · subst hEq
            simpa [hAllocHead] using hHeadCap
          · calc
              (alloc i : ℕ) = (residualW i : ℕ) := by
                simp [alloc, headVal, Function.update, hEq]
              _ ≤ cap i := hResidualCap i
        · constructor
          · have hResidualHeadZero : (residualW head.1 : ℕ) = 0 := by
              by_contra hNe
              have hPos' : 0 < (residualW head.1 : ℕ) := Nat.pos_of_ne_zero hNe
              exact hHeadFresh ((mem_supportSet_iff).2 hPos')
            have hSumAlloc :
                ∑ i, (alloc i : ℕ) =
                  Finset.sum (Finset.univ.erase head.1) (fun i : Fin n => (alloc i : ℕ)) + head.2 := by
              calc
                ∑ i, (alloc i : ℕ)
                    = Finset.sum (Finset.univ.erase head.1) (fun i : Fin n => (alloc i : ℕ)) + (alloc head.1 : ℕ) := by
                        symm
                        simpa using
                          (Finset.sum_erase_add (s := Finset.univ) (f := fun i : Fin n => (alloc i : ℕ))
                            (by simp : head.1 ∈ Finset.univ))
                _ = Finset.sum (Finset.univ.erase head.1) (fun i : Fin n => (alloc i : ℕ)) + head.2 := by
                    rw [hAllocHead]
            have hEraseEq :
                Finset.sum (Finset.univ.erase head.1) (fun i : Fin n => (alloc i : ℕ)) =
                  Finset.sum (Finset.univ.erase head.1) (fun i : Fin n => (residualW i : ℕ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hiNe : i ≠ head.1 := (Finset.mem_erase.mp hi).1
              simp [alloc, headVal, Function.update, hiNe]
            have hResidualErase :
                Finset.sum (Finset.univ.erase head.1) (fun i : Fin n => (residualW i : ℕ)) =
                  ∑ i, (residualW i : ℕ) := by
              calc
                Finset.sum (Finset.univ.erase head.1) (fun i : Fin n => (residualW i : ℕ))
                    = Finset.sum (Finset.univ.erase head.1) (fun i : Fin n => (residualW i : ℕ)) + (residualW head.1 : ℕ) := by
                        simp [hResidualHeadZero]
                _ = ∑ i, (residualW i : ℕ) := by
                    simpa using
                      (Finset.sum_erase_add (s := Finset.univ) (f := fun i : Fin n => (residualW i : ℕ))
                        (by simp : head.1 ∈ Finset.univ))
            have hSum' : head.2 + (Q - head.2) = Q := by omega
            calc
              ∑ i, (alloc i : ℕ)
                  = Finset.sum (Finset.univ.erase head.1) (fun i : Fin n => (alloc i : ℕ)) + head.2 := hSumAlloc
              _ = (∑ i, (residualW i : ℕ)) + head.2 := by rw [hEraseEq, hResidualErase]
              _ = (Q - head.2) + head.2 := by rw [hResidualSum]
              _ = Q := by omega
          · rw [← supportLegs_length (alloc := alloc), hSupportLegsAlloc]
            simpa using hLen
      exact ⟨alloc, hAllocFeasible, hSupportLegsAlloc⟩

theorem quoted_amountOut_sum_eq_target
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {quotedLegs : List (QuotedLeg n)}
    (hQuoted : QuotedStructurallyReachable quoteIn cap Q quotedLegs) :
    ((supportOfQuotedLegs quotedLegs).map Prod.snd).sum = Q := by
  induction hQuoted with
  | nil =>
      rfl
  | @cons Q head tail _hLower _hUpper _hQuote _hTail ih =>
      calc
        ((supportOfQuotedLegs (head :: tail)).map Prod.snd).sum
            = head.amountOut + ((supportOfQuotedLegs tail).map Prod.snd).sum := by
                simp [supportOfQuotedLegs]
        _ = head.amountOut + (Q - head.amountOut) := by rw [ih]
        _ = Q := by omega

theorem quoted_support_positive
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {quotedLegs : List (QuotedLeg n)}
    (hQuoted : QuotedStructurallyReachable quoteIn cap Q quotedLegs) :
    ∀ leg ∈ supportOfQuotedLegs quotedLegs, 0 < leg.2 := by
  induction hQuoted with
  | nil =>
      intro leg hMem
      simp [supportOfQuotedLegs] at hMem
  | @cons Q head tail hLower _hUpper _hQuote hTail ih =>
      intro leg hMem
      simp [supportOfQuotedLegs] at hMem
      rcases hMem with rfl | hMemTail
      · exact lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_left _ _) hLower)
      · rcases hMemTail with ⟨leg', hInTail, hEq⟩
        cases hEq
        exact ih _ (List.mem_map.mpr ⟨leg', hInTail, rfl⟩)

theorem quoted_support_cap_bounded
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {quotedLegs : List (QuotedLeg n)}
    (hQuoted : QuotedStructurallyReachable quoteIn cap Q quotedLegs) :
    ∀ leg ∈ supportOfQuotedLegs quotedLegs, leg.2 ≤ cap leg.1 := by
  induction hQuoted with
  | nil =>
      intro leg hMem
      simp [supportOfQuotedLegs] at hMem
  | @cons Q head tail _hLower hUpper _hQuote hTail ih =>
      intro leg hMem
      simp [supportOfQuotedLegs] at hMem
      rcases hMem with rfl | hMemTail
      · exact le_trans hUpper (min_le_left _ _)
      · rcases hMemTail with ⟨leg', hInTail, hEq⟩
        cases hEq
        exact ih _ (List.mem_map.mpr ⟨leg', hInTail, rfl⟩)

theorem exists_alloc_of_sorted_quoted_presentation
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    {quotedLegs : List (QuotedLeg n)}
    (hQuoted : QuotedStructurallyReachable quoteIn cap Q quotedLegs)
    (hSorted : ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT)
    (hLen : quotedLegs.length ≤ maxLegs) :
    ∃ alloc : Alloc n Q, Feasible cap maxLegs alloc ∧
      supportOfQuotedLegs quotedLegs = supportLegs alloc := by
  have hLenSupport : (supportOfQuotedLegs quotedLegs).length ≤ maxLegs := by
    simpa [supportOfQuotedLegs] using hLen
  rcases exists_alloc_of_sorted_support_presentation
      (legs := supportOfQuotedLegs quotedLegs)
      hSorted
      hLenSupport
      (quoted_amountOut_sum_eq_target hQuoted)
      (quoted_support_positive hQuoted)
      (quoted_support_cap_bounded hQuoted) with
    ⟨alloc, hFeas, hLegs⟩
  exact ⟨alloc, hFeas, hLegs.symm⟩

end ExactOutManyPoolQuotedPathRealization
end ZenoDEX
end TauSwap
