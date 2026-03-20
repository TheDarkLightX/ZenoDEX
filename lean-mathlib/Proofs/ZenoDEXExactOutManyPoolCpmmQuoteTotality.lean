import Mathlib.Tactic
import Proofs.CpmmSwapV8ExactOutMinimality
import Proofs.ZenoDEXExactOutManyPoolOrderedQuotedPresentationBridge
import Proofs.ZenoDEXExactOutManyPoolQuotedWitnessStreamBridge
import Proofs.ZenoDEXExactOutManyPoolQuotedPathStreamBridge

/-!
# ZenoDEX Exact-Out Many-Pool CPMM Quote Totality

This file removes one local assumption from the quoted-presentation bridge in
the CPMM-only audited setting.

It formalizes the per-pool CPMM exact-out quote used by the runtime and proves
that it satisfies `QuoteTotalOnPositiveBounded` for outputs bounded by
`reserveOut - 1`, assuming positive input reserves and `fee_bps < 10000`.

That is enough to specialize the previous quoted-presentation bridge:

- the CPMM audited regime no longer needs an abstract quote-totality axiom,
- the remaining local generator-side gap is only quoted-path presentation into
  the emitted candidate stream.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolCpmmQuoteTotality

open TauSwap.CPMM.V8
open ExactOutRouteCertificate
open ExactOutManyPoolSelectedDomainCertifiedBridge
open ExactOutManyPoolQuotedPresentationBridge
open ExactOutManyPoolOrderedQuotedPresentationBridge
open ExactOutManyPoolQuotedWitnessStreamBridge
open TauSwap.ZenoDEX.ExactOutManyPoolSelectedDomainCompleteness
open TauSwap.ZenoDEX.ExactOutManyPoolSupportPresentation
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedStructuralReachability

abbrev Candidate := ExactOutRouteCertificate.Candidate
abbrev DomainInputs := ExactOutManyPoolQuotedPresentationBridge.DomainInputs
abbrev GuardInputs := ExactOutManyPoolQuotedPresentationBridge.GuardInputs

abbrev BPS : Nat := 10000

structure CpmmPool where
  reserveIn : Nat
  reserveOut : Nat
  feeBps : Nat
deriving DecidableEq, Repr

def capOut (pool : CpmmPool) : Nat :=
  pool.reserveOut - 1

def grossInRequired (pool : CpmmPool) (amountOut : Nat) : Nat :=
  let netReq : Nat := (pool.reserveIn * amountOut) ⌈/⌉ (pool.reserveOut - amountOut)
  (netReq * BPS) ⌈/⌉ (BPS - pool.feeBps)

def quoteIn (pools : Fin n → CpmmPool) (i : Fin n) (amountOut : Nat) : Option Nat :=
  if amountOut = 0 then
    some 0
  else if 0 < (pools i).reserveIn then
    if amountOut < (pools i).reserveOut then
      if (pools i).feeBps < BPS then
        some (grossInRequired (pools i) amountOut)
      else
        none
    else
      none
  else
    none

theorem grossInRequired_pos
    {pool : CpmmPool}
    {amountOut : Nat}
    (hRin : 0 < pool.reserveIn)
    (hFee : pool.feeBps < BPS)
    (hPos : 0 < amountOut)
    (hOut : amountOut < pool.reserveOut) :
    0 < grossInRequired pool amountOut := by
  unfold grossInRequired
  have hDenOut : 0 < pool.reserveOut - amountOut := Nat.sub_pos_of_lt hOut
  have hNumPos : 0 < pool.reserveIn * amountOut := Nat.mul_pos hRin hPos
  have hNetReqPos : 0 < (pool.reserveIn * amountOut) ⌈/⌉ (pool.reserveOut - amountOut) := by
    by_contra hNot
    have hZero : (pool.reserveIn * amountOut) ⌈/⌉ (pool.reserveOut - amountOut) = 0 :=
      Nat.eq_zero_of_not_pos hNot
    have hLe : pool.reserveIn * amountOut ≤ (pool.reserveOut - amountOut) * 0 := by
      exact (ceilDiv_le_iff_le_mul hDenOut).1 (by simpa [hZero])
    omega
  have hFeeDen : 0 < BPS - pool.feeBps := by
    omega
  have hGrossNumPos : 0 < ((pool.reserveIn * amountOut) ⌈/⌉ (pool.reserveOut - amountOut)) * BPS := by
    exact Nat.mul_pos hNetReqPos (by decide : 0 < BPS)
  by_contra hNot
  have hZero :
      (((pool.reserveIn * amountOut) ⌈/⌉ (pool.reserveOut - amountOut)) * BPS) ⌈/⌉
        (BPS - pool.feeBps) = 0 :=
    Nat.eq_zero_of_not_pos hNot
  have hLe :
      ((pool.reserveIn * amountOut) ⌈/⌉ (pool.reserveOut - amountOut)) * BPS ≤
        (BPS - pool.feeBps) * 0 := by
    exact (ceilDiv_le_iff_le_mul hFeeDen).1 (by simpa [hZero])
  omega

theorem grossInRequired_satisfies_exact_out
    {pool : CpmmPool}
    {amountOut : Nat}
    (hRin : 0 < pool.reserveIn)
    (hFee : pool.feeBps < BPS)
    (hOut : amountOut < pool.reserveOut) :
    let gross := grossInRequired pool amountOut
    let netActual := gross - ((gross * pool.feeBps) ⌈/⌉ BPS)
    let outQuote := (pool.reserveOut * netActual) / (pool.reserveIn + netActual)
    amountOut ≤ outQuote := by
  simpa [grossInRequired, BPS] using
    (swap_exact_out_sufficient_and_minimal
      (rin := pool.reserveIn)
      (rout := pool.reserveOut)
      (aout := amountOut)
      (fee_bps := pool.feeBps)
      hRin
      hOut
      hFee).1

theorem quoteIn_eq_some_grossInRequired_of_pos_le_cap
    {n : ℕ}
    (pools : Fin n → CpmmPool)
    {i : Fin n}
    {amountOut : Nat}
    (hRin : 0 < (pools i).reserveIn)
    (hFee : (pools i).feeBps < BPS)
    (hPos : 0 < amountOut)
    (hBound : amountOut ≤ capOut (pools i)) :
    quoteIn pools i amountOut = some (grossInRequired (pools i) amountOut) := by
  have hOut : amountOut < (pools i).reserveOut := by
    dsimp [capOut] at hBound
    omega
  unfold quoteIn
  simp [hPos.ne', hRin, hOut, hFee, grossInRequired]

theorem quoteTotalOnPositiveBounded
    {n : ℕ}
    (pools : Fin n → CpmmPool)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS) :
    QuoteTotalOnPositiveBounded
      (quoteIn pools)
      (fun i => capOut (pools i)) := by
  intro i amountOut hPos hBound
  have hOut : amountOut < (pools i).reserveOut := by
    dsimp [capOut] at hBound
    omega
  exact ⟨
    grossInRequired (pools i) amountOut,
    grossInRequired_pos (hRin i) (hFee i) hPos hOut,
    quoteIn_eq_some_grossInRequired_of_pos_le_cap
      pools (hRin i) (hFee i) hPos hBound
  ⟩

theorem presentedBy_of_cpmm_quoted_presentation
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (inputs : GuardInputs)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hQuotedPresented :
      QuotedPresentedBy
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        inputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable
            (quoteIn pools)
            (fun i => capOut (pools i))
            Q
            quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    PresentedBy
      (fun alloc => Feasible (fun i => capOut (pools i)) maxLegs alloc)
      candidateOf
      inputs := by
  exact ExactOutManyPoolQuotedPresentationBridge.presentedBy_of_quoteTotal_and_quoted_presentation
    (quoteIn := quoteIn pools)
    (cap := fun i => capOut (pools i))
    (candidateOf := candidateOf)
    (candidateOfQuoted := candidateOfQuoted)
    (inputs := inputs)
    (quoteTotalOnPositiveBounded pools hRin hFee)
    hQuotedPresented
    hCompat

theorem packetOk_implies_feasible_quote_and_minimality_of_cpmm_quoted_presentation
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hQuotedPresented :
      QuotedPresentedBy
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        guardInputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable
            (quoteIn pools)
            (fun i => capOut (pools i))
            Q
            quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∃ allocStar,
      Feasible (fun i => capOut (pools i)) maxLegs allocStar ∧
        candidateOf allocStar = guardInputs.runtimeChoice ∧
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some guardInputs.runtimeChoice ∧
        ∀ alloc,
          Feasible (fun i => capOut (pools i)) maxLegs alloc →
            keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  exact ExactOutManyPoolQuotedPresentationBridge.packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_quoted_presentation
    (quoteIn := quoteIn pools)
    (cap := fun i => capOut (pools i))
    (candidateOf := candidateOf)
    (candidateOfQuoted := candidateOfQuoted)
    (domainInputs := domainInputs)
    (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hQuotedPresented
      hCompat

theorem packetOk_implies_feasible_quote_and_minimality_of_cpmm_witnessStreamCover
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses :
      List (QuotedWitness
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      WitnessStreamCovers
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        witnesses
        guardInputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable
            (quoteIn pools)
            (fun i => capOut (pools i))
            Q
            quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∃ allocStar,
      Feasible (fun i => capOut (pools i)) maxLegs allocStar ∧
        candidateOf allocStar = guardInputs.runtimeChoice ∧
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some guardInputs.runtimeChoice ∧
        ∀ alloc,
          Feasible (fun i => capOut (pools i)) maxLegs alloc →
            keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  exact
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_witnessStreamCover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover
      hCompat

theorem packetOk_implies_feasible_quote_and_minimality_of_cpmm_pathWitnessStreamCover
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses :
      List (ExactOutManyPoolQuotedPathStreamBridge.QuotedPathWitness
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      ExactOutManyPoolQuotedPathStreamBridge.PathWitnessStreamCovers
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        witnesses
        guardInputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable
            (quoteIn pools)
            (fun i => capOut (pools i))
            Q
            quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∃ allocStar,
      Feasible (fun i => capOut (pools i)) maxLegs allocStar ∧
        candidateOf allocStar = guardInputs.runtimeChoice ∧
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some guardInputs.runtimeChoice ∧
        ∀ alloc,
          Feasible (fun i => capOut (pools i)) maxLegs alloc →
            keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  exact
    ExactOutManyPoolQuotedPathStreamBridge.packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_pathWitnessStreamCover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover
      hCompat

theorem packetOk_implies_feasible_quote_and_minimality_of_cpmm_witnessStreamSetCover
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses :
      List (QuotedWitness
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      WitnessStreamSetCovers
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        witnesses
        guardInputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable
            (quoteIn pools)
            (fun i => capOut (pools i))
            Q
            quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∃ allocStar,
      Feasible (fun i => capOut (pools i)) maxLegs allocStar ∧
        candidateOf allocStar = guardInputs.runtimeChoice ∧
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some guardInputs.runtimeChoice ∧
        ∀ alloc,
          Feasible (fun i => capOut (pools i)) maxLegs alloc →
            keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  exact
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_witnessStreamSetCover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover
      hCompat

theorem packetOk_implies_feasible_quote_and_minimality_of_cpmm_pathWitnessStreamSetCover
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses :
      List (ExactOutManyPoolQuotedPathStreamBridge.QuotedPathWitness
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      ExactOutManyPoolQuotedPathStreamBridge.PathWitnessStreamSetCovers
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        witnesses
        guardInputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable
            (quoteIn pools)
            (fun i => capOut (pools i))
            Q
            quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∃ allocStar,
      Feasible (fun i => capOut (pools i)) maxLegs allocStar ∧
        candidateOf allocStar = guardInputs.runtimeChoice ∧
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some guardInputs.runtimeChoice ∧
        ∀ alloc,
          Feasible (fun i => capOut (pools i)) maxLegs alloc →
            keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  exact
    ExactOutManyPoolQuotedPathStreamBridge.packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_pathWitnessStreamSetCover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover
      hCompat

theorem packetOk_implies_feasible_quote_and_minimality_of_cpmm_ordered_path_list_cover
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
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
      ExactOutManyPoolOrderedQuotedPresentationBridge.OrderedQuotedPathListCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        guardInputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable
            (quoteIn pools)
            (fun i => capOut (pools i))
            Q
            quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∃ allocStar,
      Feasible (fun i => capOut (pools i)) maxLegs allocStar ∧
        candidateOf allocStar = guardInputs.runtimeChoice ∧
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some guardInputs.runtimeChoice ∧
        ∀ alloc,
          Feasible (fun i => capOut (pools i)) maxLegs alloc →
            keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  exact
    ExactOutManyPoolOrderedQuotedPresentationBridge.packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_list_cover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover
      hCompat

end ExactOutManyPoolCpmmQuoteTotality
end Routing
end TauSwap
