import Proofs.ZenoDEXExactOutManyPoolCpmmQuoteTotality
import Proofs.ZenoDEXExactOutManyPoolOrderedQuotedPresentationBridge

open scoped Classical

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolOrderedQuotedCandidateBridge

open ExactOutRouteCertificate
open ExactOutManyPoolSelectedDomainCertifiedBridge
open ExactOutManyPoolOrderedQuotedPresentationBridge
open TauSwap.ZenoDEX.ExactOutManyPoolSelectedDomainCompleteness
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedStructuralReachability
open TauSwap.ZenoDEX.ExactOutManyPoolSupportPresentation
open TauSwap.Routing.ExactOutManyPoolCpmmQuoteTotality

abbrev Candidate := ExactOutRouteCertificate.Candidate
abbrev DomainInputs := ExactOutManyPoolOrderedQuotedPresentationBridge.DomainInputs
abbrev GuardInputs := ExactOutManyPoolOrderedQuotedPresentationBridge.GuardInputs

noncomputable section

/-!
# ZenoDEX Exact-Out Many-Pool Ordered Quoted Candidate Bridge

This file removes the remaining abstract compatibility axiom from the
ordered-path packet bridge.

If the quote oracle is deterministic, then a feasible audited allocation has a
unique quoted recursive path realizing its support presentation. That lets the
proof define a canonical candidate map directly from `candidateOfQuoted`,
instead of carrying a separate `candidateOf` plus `hCompat` hypothesis.
-/

/-- Feasible audited-domain image under a candidate map. -/
def feasibleCandidateSet
    {n Q : ℕ}
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOf : Alloc n Q → Candidate) : Finset Candidate :=
  (feasibleSet cap maxLegs).image candidateOf

theorem keyLe_antisymm {a b : Candidate}
    (hAB : keyLe a b) (hBA : keyLe b a) :
    a = b := by
  cases a with
  | mk aIdx aKey =>
    cases b with
    | mk bIdx bKey =>
      simp [keyLe] at hAB hBA
      rcases hAB with hAB | ⟨hKeyAB, hIdxAB⟩
      · rcases hBA with hBA | ⟨hKeyBA, _⟩
        · exact False.elim (Nat.lt_asymm hAB hBA)
        · have : False := by
            simp [hKeyBA] at hAB
          exact False.elim this
      · rcases hBA with hBA | ⟨_hKeyBA, hIdxBA⟩
        · have : False := by
            simp [hKeyAB] at hBA
          exact False.elim this
        · have hIdx : aIdx = bIdx := Nat.le_antisymm hIdxAB hIdxBA
          cases hKeyAB
          cases hIdx
          rfl

theorem quotedLegs_eq_of_supportEq_of_reachable
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {quotedLegs₁ quotedLegs₂ : List (QuotedLeg n)}
    (hQuoted₁ : QuotedStructurallyReachable quoteIn cap Q quotedLegs₁)
    (hQuoted₂ : QuotedStructurallyReachable quoteIn cap Q quotedLegs₂)
    (hSupport : supportOfQuotedLegs quotedLegs₁ = supportOfQuotedLegs quotedLegs₂) :
    quotedLegs₁ = quotedLegs₂ := by
  revert quotedLegs₂
  induction hQuoted₁ with
  | nil =>
      intro quotedLegs₂ hQuoted₂ hSupport
      cases hQuoted₂ with
      | nil =>
          rfl
      | cons =>
          simp [supportOfQuotedLegs] at hSupport
  | @cons Q head₁ tail₁ hLower₁ hUpper₁ hQuote₁ hTail₁ ih =>
      intro quotedLegs₂ hQuoted₂ hSupport
      cases hQuoted₂ with
      | nil =>
          simp [supportOfQuotedLegs] at hSupport
      | @cons _ head₂ tail₂ hLower₂ hUpper₂ hQuote₂ hTail₂ =>
          have hCons :
              (head₁.poolIdx, head₁.amountOut) :: supportOfQuotedLegs tail₁ =
                (head₂.poolIdx, head₂.amountOut) :: supportOfQuotedLegs tail₂ := by
            simpa [supportOfQuotedLegs] using hSupport
          rcases List.cons.inj hCons with ⟨hHeadPair, hTailSupport⟩
          have hPool : head₁.poolIdx = head₂.poolIdx := by
            exact congrArg Prod.fst hHeadPair
          have hOut : head₁.amountOut = head₂.amountOut := by
            exact congrArg Prod.snd hHeadPair
          have hIn : head₁.amountIn = head₂.amountIn := by
            have hQuote₂' :
                quoteIn head₁.poolIdx head₁.amountOut = some head₂.amountIn := by
              simpa [hPool, hOut] using hQuote₂
            have hSome : some head₁.amountIn = some head₂.amountIn := by
              exact hQuote₁.symm.trans hQuote₂'
            exact Option.some.inj hSome
          have hTail₂' :
              QuotedStructurallyReachable quoteIn cap (Q - head₁.amountOut) tail₂ := by
            simpa [hOut] using hTail₂
          have hTailEq : tail₁ = tail₂ :=
            ih hTail₂' hTailSupport
          cases head₁
          cases head₂
          simp at hPool hOut hIn
          cases hPool
          cases hOut
          cases hIn
          simp [hTailEq]

/-- Canonical allocation-to-candidate map obtained by quoting the feasible
support presentation of an allocation. Outside the feasible audited domain it
falls back to `candidateOfQuoted []`, but all bridge theorems use it only under
feasibility premises. -/
noncomputable def canonicalCandidateOfQuoted
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap) :
    Alloc n Q → Candidate :=
  fun alloc =>
    if hFeas : Feasible cap maxLegs alloc then
      candidateOfQuoted <|
        Classical.choose <|
          quoted_of_feasible_supportLegs
            (quoteIn := quoteIn)
            (cap := cap)
            (alloc := alloc)
            hQuoteTotal
            hFeas
    else
      candidateOfQuoted []

theorem canonicalCandidateOfQuoted_eq_candidateOfQuoted
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    {alloc : Alloc n Q}
    (hFeas : Feasible cap maxLegs alloc)
    {quotedLegs : List (QuotedLeg n)}
    (hSupport : supportOfQuotedLegs quotedLegs = supportLegs alloc)
    (hQuoted : QuotedStructurallyReachable quoteIn cap Q quotedLegs) :
    canonicalCandidateOfQuoted
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        hQuoteTotal
        alloc =
      candidateOfQuoted quotedLegs := by
  by_cases h : Feasible cap maxLegs alloc
  · rw [canonicalCandidateOfQuoted, dif_pos h]
    let hChosen :=
      quoted_of_feasible_supportLegs
        (quoteIn := quoteIn)
        (cap := cap)
        (alloc := alloc)
        hQuoteTotal
        h
    let chosenLegs : List (QuotedLeg n) := Classical.choose hChosen
    have hChosenSupport : supportOfQuotedLegs chosenLegs = supportLegs alloc :=
      (Classical.choose_spec hChosen).1
    have hChosenQuoted : QuotedStructurallyReachable quoteIn cap Q chosenLegs :=
      (Classical.choose_spec hChosen).2
    have hChosenEq : chosenLegs = quotedLegs :=
      quotedLegs_eq_of_supportEq_of_reachable
        hChosenQuoted
        hQuoted
        (hChosenSupport.trans hSupport.symm)
    simp [chosenLegs, hChosenEq]
  · exact False.elim (h hFeas)

theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_list_cover_canonicalCandidate
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        guardInputs) :
    ∃ allocStar : Alloc n Q, Feasible cap maxLegs allocStar ∧
      canonicalCandidateOfQuoted
          (Q := Q)
          quoteIn
          cap
          maxLegs
          candidateOfQuoted
          hQuoteTotal
          allocStar =
        guardInputs.runtimeChoice ∧
      (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∀ alloc : Alloc n Q, Feasible cap maxLegs alloc →
        keyLe
          guardInputs.runtimeChoice
          (canonicalCandidateOfQuoted
            (Q := Q)
            quoteIn
            cap
            maxLegs
            candidateOfQuoted
            hQuoteTotal
            alloc) := by
  exact
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_list_cover
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf :=
        canonicalCandidateOfQuoted
          (Q := Q)
          quoteIn
          cap
          maxLegs
          candidateOfQuoted
          hQuoteTotal)
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      hCover
      (by
        intro alloc quotedLegs hFeas hSupport hQuoted
        exact canonicalCandidateOfQuoted_eq_candidateOfQuoted
          (candidateOfQuoted := candidateOfQuoted)
          hQuoteTotal
          hFeas
          hSupport
          hQuoted)

theorem packetOk_implies_feasible_quote_and_minimality_of_cpmm_ordered_path_list_cover_canonicalCandidate
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        guardInputs) :
    ∃ allocStar : Alloc n Q,
      Feasible (fun i => capOut (pools i)) maxLegs allocStar ∧
        canonicalCandidateOfQuoted
            (Q := Q)
            (quoteIn pools)
            (fun i => capOut (pools i))
            maxLegs
            candidateOfQuoted
            (quoteTotalOnPositiveBounded pools hRin hFee)
            allocStar =
          guardInputs.runtimeChoice ∧
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some guardInputs.runtimeChoice ∧
        ∀ alloc : Alloc n Q,
          Feasible (fun i => capOut (pools i)) maxLegs alloc →
            keyLe
              guardInputs.runtimeChoice
              (canonicalCandidateOfQuoted
                (Q := Q)
                (quoteIn pools)
                (fun i => capOut (pools i))
                maxLegs
                candidateOfQuoted
                (quoteTotalOnPositiveBounded pools hRin hFee)
                alloc) := by
  exact
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_list_cover_canonicalCandidate
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover

theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_set_cover_canonicalCandidate
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      ExactOutManyPoolOrderedQuotedPresentationBridge.OrderedQuotedPathSetCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        guardInputs) :
    ∃ allocStar : Alloc n Q, Feasible cap maxLegs allocStar ∧
      canonicalCandidateOfQuoted
          (Q := Q)
          quoteIn
          cap
          maxLegs
          candidateOfQuoted
          hQuoteTotal
          allocStar =
        guardInputs.runtimeChoice ∧
      (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∀ alloc : Alloc n Q, Feasible cap maxLegs alloc →
        keyLe
          guardInputs.runtimeChoice
          (canonicalCandidateOfQuoted
            (Q := Q)
            quoteIn
            cap
            maxLegs
            candidateOfQuoted
            hQuoteTotal
            alloc) := by
  exact
    ExactOutManyPoolOrderedQuotedPresentationBridge.packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_set_cover
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf :=
        canonicalCandidateOfQuoted
          (Q := Q)
          quoteIn
          cap
          maxLegs
          candidateOfQuoted
          hQuoteTotal)
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      hCover
      (by
        intro alloc quotedLegs hFeas hSupport hQuoted
        exact canonicalCandidateOfQuoted_eq_candidateOfQuoted
          (candidateOfQuoted := candidateOfQuoted)
          hQuoteTotal
          hFeas
          hSupport
          hQuoted)

theorem packetOk_implies_feasible_quote_and_minimality_of_cpmm_ordered_path_set_cover_canonicalCandidate
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      ExactOutManyPoolOrderedQuotedPresentationBridge.OrderedQuotedPathSetCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        guardInputs) :
    ∃ allocStar : Alloc n Q,
      Feasible (fun i => capOut (pools i)) maxLegs allocStar ∧
        canonicalCandidateOfQuoted
            (Q := Q)
            (quoteIn pools)
            (fun i => capOut (pools i))
            maxLegs
            candidateOfQuoted
            (quoteTotalOnPositiveBounded pools hRin hFee)
            allocStar =
          guardInputs.runtimeChoice ∧
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some guardInputs.runtimeChoice ∧
        ∀ alloc : Alloc n Q,
          Feasible (fun i => capOut (pools i)) maxLegs alloc →
            keyLe
              guardInputs.runtimeChoice
              (canonicalCandidateOfQuoted
                (Q := Q)
                (quoteIn pools)
                (fun i => capOut (pools i))
                maxLegs
                candidateOfQuoted
                (quoteTotalOnPositiveBounded pools hRin hFee)
                alloc) := by
  exact
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_set_cover_canonicalCandidate
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover

theorem packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_ordered_path_list_cover_canonicalCandidate
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        guardInputs) :
    (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∃! cand,
        cand ∈
            feasibleCandidateSet
              cap
              maxLegs
              (canonicalCandidateOfQuoted
                (Q := Q)
                quoteIn
                cap
                maxLegs
                candidateOfQuoted
                hQuoteTotal) ∧
          ∀ y ∈
              feasibleCandidateSet
                cap
                maxLegs
                (canonicalCandidateOfQuoted
                  (Q := Q)
                  quoteIn
                  cap
                  maxLegs
                  candidateOfQuoted
                  hQuoteTotal),
            keyLe cand y := by
  rcases
      packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_list_cover_canonicalCandidate
        (quoteIn := quoteIn)
        (cap := cap)
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (domainInputs := domainInputs)
        (guardInputs := guardInputs)
        hPacket
        hQuoteTotal
        hCover with
    ⟨allocStar, hFeas, hCandStar, hQuote, hMin⟩
  let candidateOf :
      Alloc n Q → Candidate :=
    canonicalCandidateOfQuoted
      (Q := Q)
      quoteIn
      cap
      maxLegs
      candidateOfQuoted
      hQuoteTotal
  let S := feasibleCandidateSet cap maxLegs candidateOf
  have hMem : guardInputs.runtimeChoice ∈ S := by
    change
      guardInputs.runtimeChoice ∈
        (feasibleSet cap maxLegs).image candidateOf
    exact Finset.mem_image.mpr ⟨allocStar, mem_feasibleSet_of_feasible hFeas, hCandStar⟩
  have hMinSet :
      ∀ y ∈ S, keyLe guardInputs.runtimeChoice y := by
    intro y hy
    change y ∈ (feasibleSet cap maxLegs).image candidateOf at hy
    rcases Finset.mem_image.mp hy with ⟨alloc, hAllocMem, rfl⟩
    exact hMin alloc (by simpa [feasibleSet] using hAllocMem)
  constructor
  · exact hQuote
  · exact ⟨guardInputs.runtimeChoice, ⟨hMem, hMinSet⟩, by
      intro cand hCand
      have hCandLe :
          keyLe cand guardInputs.runtimeChoice :=
        hCand.2 guardInputs.runtimeChoice hMem
      have hRtLe :
          keyLe guardInputs.runtimeChoice cand :=
        hMinSet cand hCand.1
      exact keyLe_antisymm hCandLe hRtLe⟩

theorem packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_cpmm_ordered_path_list_cover_canonicalCandidate
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        guardInputs) :
    (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∃! cand,
        cand ∈
            feasibleCandidateSet
              (fun i => capOut (pools i))
              maxLegs
              (canonicalCandidateOfQuoted
                (Q := Q)
                (quoteIn pools)
                (fun i => capOut (pools i))
                maxLegs
                candidateOfQuoted
                (quoteTotalOnPositiveBounded pools hRin hFee)) ∧
          ∀ y ∈
              feasibleCandidateSet
                (fun i => capOut (pools i))
                maxLegs
                (canonicalCandidateOfQuoted
                  (Q := Q)
                  (quoteIn pools)
                  (fun i => capOut (pools i))
                  maxLegs
                  candidateOfQuoted
                  (quoteTotalOnPositiveBounded pools hRin hFee)),
            keyLe cand y := by
  exact
    packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_ordered_path_list_cover_canonicalCandidate
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover

theorem packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_ordered_path_set_cover_canonicalCandidate
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      ExactOutManyPoolOrderedQuotedPresentationBridge.OrderedQuotedPathSetCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        guardInputs) :
    (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∃! cand,
        cand ∈
            feasibleCandidateSet
              cap
              maxLegs
              (canonicalCandidateOfQuoted
                (Q := Q)
                quoteIn
                cap
                maxLegs
                candidateOfQuoted
                hQuoteTotal) ∧
          ∀ y ∈
              feasibleCandidateSet
                cap
                maxLegs
                (canonicalCandidateOfQuoted
                  (Q := Q)
                  quoteIn
                  cap
                  maxLegs
                  candidateOfQuoted
                  hQuoteTotal),
            keyLe cand y := by
  rcases
      packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_set_cover_canonicalCandidate
        (quoteIn := quoteIn)
        (cap := cap)
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (domainInputs := domainInputs)
        (guardInputs := guardInputs)
        hPacket
        hQuoteTotal
        hCover with
    ⟨allocStar, hFeas, hCandStar, hQuote, hMin⟩
  let candidateOf :
      Alloc n Q → Candidate :=
    canonicalCandidateOfQuoted
      (Q := Q)
      quoteIn
      cap
      maxLegs
      candidateOfQuoted
      hQuoteTotal
  let S := feasibleCandidateSet cap maxLegs candidateOf
  have hMem : guardInputs.runtimeChoice ∈ S := by
    change
      guardInputs.runtimeChoice ∈
        (feasibleSet cap maxLegs).image candidateOf
    exact Finset.mem_image.mpr ⟨allocStar, mem_feasibleSet_of_feasible hFeas, hCandStar⟩
  have hMinSet :
      ∀ y ∈ S, keyLe guardInputs.runtimeChoice y := by
    intro y hy
    change y ∈ (feasibleSet cap maxLegs).image candidateOf at hy
    rcases Finset.mem_image.mp hy with ⟨alloc, hAllocMem, rfl⟩
    exact hMin alloc (by simpa [feasibleSet] using hAllocMem)
  constructor
  · exact hQuote
  · exact ⟨guardInputs.runtimeChoice, ⟨hMem, hMinSet⟩, by
      intro cand hCand
      have hCandLe :
          keyLe cand guardInputs.runtimeChoice :=
        hCand.2 guardInputs.runtimeChoice hMem
      have hRtLe :
          keyLe guardInputs.runtimeChoice cand :=
        hMinSet cand hCand.1
      exact keyLe_antisymm hCandLe hRtLe⟩

theorem packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_cpmm_ordered_path_set_cover_canonicalCandidate
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      ExactOutManyPoolOrderedQuotedPresentationBridge.OrderedQuotedPathSetCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        guardInputs) :
    (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∃! cand,
        cand ∈
            feasibleCandidateSet
              (fun i => capOut (pools i))
              maxLegs
              (canonicalCandidateOfQuoted
                (Q := Q)
                (quoteIn pools)
                (fun i => capOut (pools i))
                maxLegs
                candidateOfQuoted
                (quoteTotalOnPositiveBounded pools hRin hFee)) ∧
          ∀ y ∈
              feasibleCandidateSet
                (fun i => capOut (pools i))
                maxLegs
                (canonicalCandidateOfQuoted
                  (Q := Q)
                  (quoteIn pools)
                  (fun i => capOut (pools i))
                  maxLegs
                  candidateOfQuoted
                  (quoteTotalOnPositiveBounded pools hRin hFee)),
            keyLe cand y := by
  exact
    packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_ordered_path_set_cover_canonicalCandidate
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover

end
end ExactOutManyPoolOrderedQuotedCandidateBridge
end Routing
end TauSwap
