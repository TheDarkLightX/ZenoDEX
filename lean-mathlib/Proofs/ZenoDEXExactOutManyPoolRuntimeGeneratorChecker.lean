import Proofs.SolverCheckerSeparation
import Proofs.ZenoDEXExactOutManyPoolOrderedPathWitnessShapeLadder

open scoped Classical

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolRuntimeGeneratorChecker

open Proofs.SolverCheckerSeparation
open ExactOutRouteCertificate
open ExactOutManyPoolSelectedDomainCertifiedBridge
open ExactOutManyPoolQuotedPathStreamBridge
open ExactOutManyPoolOrderedPathWitnessShapeLadder
open ExactOutManyPoolOrderedQuotedCandidateBridge
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedStructuralReachability

abbrev Candidate := ExactOutRouteCertificate.Candidate
abbrev DomainInputs := ExactOutManyPoolSelectedDomainCertifiedBridge.DomainInputs
abbrev GuardInputs := ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs

noncomputable section

/-!
# Exact-Out Runtime Generator Checker

This file instantiates the abstract solver/checker separation principle with
the exact-out many-pool ordered path-witness boundary.

It does not prove that a concrete Python/Tau runtime generator already emits a
covering witness list. Instead, it proves the reusable checker theorem:
if a generator output is accepted by the ordered witness checker, then its
decision has quote replay and is the unique canonical feasible minimum.
-/

/-- Static proof-bearing state for the exact-out checker theorem. -/
structure ExactOutCheckerState
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate) where
  domainInputs : DomainInputs
  guardInputs : GuardInputs
  packetOk :
    (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
      (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true
  quoteTotal : QuoteTotalOnPositiveBounded quoteIn cap

/-- Runtime witness payload for the semantic checker: an ordered witness list. -/
abbrev OrderedWitnessPayload
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ) :=
  List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs)

/-- The spec guaranteed by an accepted exact-out runtime decision. -/
def canonicalExactOutSpec
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    {candidateOfQuoted : List (QuotedLeg n) → Candidate}
    (_input : Unit)
    (state : ExactOutCheckerState (Q := Q) quoteIn cap maxLegs candidateOfQuoted)
    (decision : Candidate) : Prop :=
  decision = state.guardInputs.runtimeChoice ∧
    (ExactOutManyPoolGuardedQuotePacket.buildPacket state.guardInputs).quote =
      some decision ∧
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
              state.quoteTotal) ∧
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
                state.quoteTotal),
          keyLe cand y

/-- Semantic checker for an exact-out runtime generator output. -/
def orderedWitnessChecker
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    {candidateOfQuoted : List (QuotedLeg n) → Candidate}
    (_input : Unit)
    (state : ExactOutCheckerState (Q := Q) quoteIn cap maxLegs candidateOfQuoted)
    (decision : Candidate)
    (witnesses : OrderedWitnessPayload (Q := Q) quoteIn cap maxLegs) : Prop :=
  decision = state.guardInputs.runtimeChoice ∧
    OrderedPathWitnessStreamSetCovers
      quoteIn
      cap
      maxLegs
      candidateOfQuoted
      witnesses
      state.guardInputs

/-- The ordered witness checker is sound for exact-out canonicality. -/
theorem orderedWitnessChecker_sound
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    {candidateOfQuoted : List (QuotedLeg n) → Candidate} :
    PropCheckerSound
      (Input := Unit)
      (State := ExactOutCheckerState (Q := Q) quoteIn cap maxLegs candidateOfQuoted)
      (Decision := Candidate)
      (Witness := OrderedWitnessPayload (Q := Q) quoteIn cap maxLegs)
      orderedWitnessChecker
      canonicalExactOutSpec := by
  intro _input state decision witnesses hAccepted
  rcases hAccepted with ⟨hDecision, hCover⟩
  have hCanonical :=
    packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_orderedPathWitnessStreamSetCover_canonicalCandidate
      (Q := Q)
      (quoteIn := quoteIn)
      (cap := cap)
      (maxLegs := maxLegs)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses)
      (domainInputs := state.domainInputs)
      (guardInputs := state.guardInputs)
      state.packetOk
      state.quoteTotal
      hCover
  exact ⟨hDecision, by
    constructor
    · simpa [hDecision] using hCanonical.1
    · exact hCanonical.2⟩

/-- Exact-out solver shape for the ordered witness checker. -/
abbrev ExactOutSolver
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate) :=
  Solver
    Unit
    (ExactOutCheckerState (Q := Q) quoteIn cap maxLegs candidateOfQuoted)
    Candidate
    (OrderedWitnessPayload (Q := Q) quoteIn cap maxLegs)

/-- Any exact-out solver accepted by the ordered witness checker is sound. -/
theorem solver_sound_of_orderedWitnessChecker_acceptance
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    {candidateOfQuoted : List (QuotedLeg n) → Candidate}
    (solver : ExactOutSolver (Q := Q) quoteIn cap maxLegs candidateOfQuoted)
    (hSolverAccepted :
      PropSolverAccepted solver
        (orderedWitnessChecker
          (Q := Q)
          (quoteIn := quoteIn)
          (cap := cap)
          (maxLegs := maxLegs)
          (candidateOfQuoted := candidateOfQuoted))) :
    SolverSound solver
      (canonicalExactOutSpec
        (Q := Q)
        (quoteIn := quoteIn)
        (cap := cap)
        (maxLegs := maxLegs)
        (candidateOfQuoted := candidateOfQuoted)) := by
  exact
    prop_solver_sound_of_checker_sound_and_solver_accepted
      solver
      (orderedWitnessChecker
        (Q := Q)
        (quoteIn := quoteIn)
        (cap := cap)
        (maxLegs := maxLegs)
        (candidateOfQuoted := candidateOfQuoted))
      (canonicalExactOutSpec
        (Q := Q)
        (quoteIn := quoteIn)
        (cap := cap)
        (maxLegs := maxLegs)
        (candidateOfQuoted := candidateOfQuoted))
      orderedWitnessChecker_sound
      hSolverAccepted

end
end ExactOutManyPoolRuntimeGeneratorChecker
end Routing
end TauSwap
