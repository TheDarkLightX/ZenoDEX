import Mathlib

/-!
# ZenoDEX Aristotle Disaster Basis

This file promotes the strongest local theorem shapes from the Aristotle
disaster-state hardening corpus into the repo Lean tree.

The theorems are intentionally abstract. They do not claim cryptographic
soundness, oracle truth, compiler correctness, zkVM validity, Wasm containment,
or runtime liveness. They prove the load-bearing gate laws that production
claims must instantiate with concrete replay artifacts.
-/

namespace Proofs
namespace ZenoDEXAristotleDisasterBasis

/-! ## Admission and verifier context -/

structure AdmissionEvidence where
  proofEvidence : Prop
  bindingEvidence : Prop
  policyEvidence : Prop
  freshnessEvidence : Prop
  verifierContext : Prop

def AdmissionEvidence.accepted (e : AdmissionEvidence) : Prop :=
  e.proofEvidence ∧
    e.bindingEvidence ∧
    e.policyEvidence ∧
    e.freshnessEvidence ∧
    e.verifierContext

theorem admission_requires_verifier
    (e : AdmissionEvidence)
    (hMissing : ¬ e.verifierContext) :
    ¬ e.accepted := by
  intro hAccepted
  exact hMissing hAccepted.2.2.2.2

theorem reward_requires_verifier_acceptance
    (e : AdmissionEvidence)
    (claimable : Prop)
    (hClaim : claimable -> e.accepted) :
    claimable -> e.verifierContext := by
  intro h
  exact (hClaim h).2.2.2.2

/-! ## Binding integrity -/

structure Commitment (H : Type*) where
  claimId : H
  statementHash : H
  assumptionsHash : H
  verifierId : H
  policyRoot : H
  toolchainId : H
  inputRoot : H
  outputRoot : H
  deriving Repr

structure BindingCheck where
  checkClaimId : Bool
  checkStatementHash : Bool
  checkAssumptionsHash : Bool
  checkVerifierId : Bool
  checkPolicyRoot : Bool
  checkToolchainId : Bool
  checkInputRoot : Bool
  checkOutputRoot : Bool

def BindingCheck.passes {H : Type*}
    (bc : BindingCheck) (c1 c2 : Commitment H) : Prop :=
  (bc.checkClaimId = true -> c1.claimId = c2.claimId) ∧
    (bc.checkStatementHash = true -> c1.statementHash = c2.statementHash) ∧
    (bc.checkAssumptionsHash = true -> c1.assumptionsHash = c2.assumptionsHash) ∧
    (bc.checkVerifierId = true -> c1.verifierId = c2.verifierId) ∧
    (bc.checkPolicyRoot = true -> c1.policyRoot = c2.policyRoot) ∧
    (bc.checkToolchainId = true -> c1.toolchainId = c2.toolchainId) ∧
    (bc.checkInputRoot = true -> c1.inputRoot = c2.inputRoot) ∧
    (bc.checkOutputRoot = true -> c1.outputRoot = c2.outputRoot)

def BindingCheck.full : BindingCheck :=
  ⟨true, true, true, true, true, true, true, true⟩

def BindingCheck.none : BindingCheck :=
  ⟨false, false, false, false, false, false, false, false⟩

theorem full_binding_iff_match {H : Type*}
    (c1 c2 : Commitment H) :
    BindingCheck.full.passes c1 c2 ↔ c1 = c2 := by
  constructor
  · intro h
    cases c1
    cases c2
    simp [BindingCheck.full, BindingCheck.passes] at h
    simp [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2]
  · intro h
    subst h
    simp [BindingCheck.full, BindingCheck.passes]

theorem binding_mismatch_blocks_statement_hash {H : Type*}
    (bc : BindingCheck) (c1 c2 : Commitment H)
    (hCheck : bc.checkStatementHash = true)
    (hMismatch : c1.statementHash ≠ c2.statementHash) :
    ¬ bc.passes c1 c2 := by
  intro hPass
  exact hMismatch (hPass.2.1 hCheck)

theorem partial_binding_allows_mismatch {H : Type*}
    (a b : H) (hNe : a ≠ b) :
    ∃ (bc : BindingCheck) (c1 c2 : Commitment H),
      c1 ≠ c2 ∧ bc.passes c1 c2 := by
  let c1 : Commitment H := ⟨a, a, a, a, a, a, a, a⟩
  let c2 : Commitment H := ⟨b, b, b, b, b, b, b, b⟩
  exact ⟨BindingCheck.none, c1, c2,
    by
      intro hEq
      exact hNe (congrArg Commitment.claimId hEq),
    by
      simp [BindingCheck.none, BindingCheck.passes]⟩

/-! ## O5 independence -/

structure CrosscheckClaim (ClaimId VerifierId ProofKind Root : Type*) where
  claimId : ClaimId
  verifierId : VerifierId
  proofKind : ProofKind
  inputRoot : Root
  outputRoot : Root

def distinctVerifiers {ClaimId VerifierId ProofKind Root : Type*}
    (primary : CrosscheckClaim ClaimId VerifierId ProofKind Root)
    (crosschecks : List (CrosscheckClaim ClaimId VerifierId ProofKind Root)) :
    Prop :=
  (∀ c ∈ crosschecks, c.verifierId ≠ primary.verifierId) ∧
    crosschecks.Pairwise (fun c1 c2 => c1.verifierId ≠ c2.verifierId)

def rootsMatch {ClaimId VerifierId ProofKind Root : Type*}
    (primary : CrosscheckClaim ClaimId VerifierId ProofKind Root)
    (crosschecks : List (CrosscheckClaim ClaimId VerifierId ProofKind Root)) :
    Prop :=
  ∀ c ∈ crosschecks,
    c.inputRoot = primary.inputRoot ∧ c.outputRoot = primary.outputRoot

def dagAcyclicSimple {ClaimId : Type*}
    (deps : List (ClaimId × ClaimId)) : Prop :=
  (∀ p ∈ deps, p.1 ≠ p.2) ∧
    (∀ p ∈ deps, (p.2, p.1) ∉ deps)

theorem weak_verifier_count_rejects
    {ClaimId VerifierId ProofKind Root : Type*}
    (primary : CrosscheckClaim ClaimId VerifierId ProofKind Root)
    (crosschecks : List (CrosscheckClaim ClaimId VerifierId ProofKind Root))
    (hSame : ∃ c ∈ crosschecks, c.verifierId = primary.verifierId) :
    ¬ distinctVerifiers primary crosschecks := by
  intro hDistinct
  rcases hSame with ⟨c, hMem, hEq⟩
  exact hDistinct.1 c hMem hEq

theorem root_drift_rejects
    {ClaimId VerifierId ProofKind Root : Type*}
    (primary : CrosscheckClaim ClaimId VerifierId ProofKind Root)
    (crosschecks : List (CrosscheckClaim ClaimId VerifierId ProofKind Root))
    (hDrift : ∃ c ∈ crosschecks,
      c.inputRoot ≠ primary.inputRoot ∨ c.outputRoot ≠ primary.outputRoot) :
    ¬ rootsMatch primary crosschecks := by
  intro hRoots
  rcases hDrift with ⟨c, hMem, hBad⟩
  exact hBad.elim
    (fun hInput => hInput (hRoots c hMem).1)
    (fun hOutput => hOutput (hRoots c hMem).2)

theorem acyclic_no_self_support {ClaimId : Type*}
    (deps : List (ClaimId × ClaimId))
    (hAcyclic : dagAcyclicSimple deps)
    (claim : ClaimId) :
    (claim, claim) ∉ deps := by
  intro hMem
  exact hAcyclic.1 (claim, claim) hMem rfl

/-! ## Oracle consumption binding -/

structure OracleReport where
  sourceId : Nat
  value : Int
  timestamp : Nat
  queryId : Nat

structure OracleAggregate where
  queryId : Nat
  medianValue : Int
  windowStart : Nat
  windowEnd : Nat
  sourceCount : Nat

def reportFresh (r : OracleReport) (windowStart windowEnd : Nat) : Prop :=
  windowStart ≤ r.timestamp ∧ r.timestamp ≤ windowEnd

structure ConsumerBinding where
  expectedQueryId : Nat
  expectedValue : Int
  expectedWindowStart : Nat
  expectedWindowEnd : Nat

def ConsumerBinding.matches
    (cb : ConsumerBinding) (agg : OracleAggregate) : Prop :=
  cb.expectedQueryId = agg.queryId ∧
    cb.expectedValue = agg.medianValue ∧
    cb.expectedWindowStart = agg.windowStart ∧
    cb.expectedWindowEnd = agg.windowEnd

theorem stale_report_rejected
    (r : OracleReport) (windowStart windowEnd : Nat)
    (hStale : r.timestamp < windowStart ∨ r.timestamp > windowEnd) :
    ¬ reportFresh r windowStart windowEnd := by
  intro hFresh
  rcases hStale with hLow | hHigh
  · exact (Nat.not_le_of_gt hLow) hFresh.1
  · exact (Nat.not_le_of_gt hHigh) hFresh.2

theorem mismatched_query_blocks
    (cb : ConsumerBinding) (agg : OracleAggregate)
    (hMismatch : cb.expectedQueryId ≠ agg.queryId) :
    ¬ cb.matches agg := by
  intro hMatches
  exact hMismatch hMatches.1

theorem mismatched_value_blocks
    (cb : ConsumerBinding) (agg : OracleAggregate)
    (hMismatch : cb.expectedValue ≠ agg.medianValue) :
    ¬ cb.matches agg := by
  intro hMatches
  exact hMismatch hMatches.2.1

/-! ## ProofMining reward accounting -/

structure RewardState where
  poolBalance : Nat
  claimedSet : Finset Nat
  totalBudget : Nat
  totalPaid : Nat

structure RewardClaim where
  nonce : Nat
  proposalHash : Nat
  minerId : Nat
  rewardAmount : Nat
  proofAccepted : Prop
  bindingOK : Prop
  policyOK : Prop

def claimUnique (s : RewardState) (nonce : Nat) : Prop :=
  nonce ∉ s.claimedSet

def processRewardClaim (s : RewardState) (c : RewardClaim) : RewardState :=
  { s with
    poolBalance := s.poolBalance - c.rewardAmount
    claimedSet := s.claimedSet ∪ {c.nonce}
    totalPaid := s.totalPaid + c.rewardAmount }

theorem reward_conservation
    (s : RewardState) (c : RewardClaim)
    (_hSufficient : c.rewardAmount ≤ s.poolBalance) :
    (processRewardClaim s c).poolBalance = s.poolBalance - c.rewardAmount := by
  rfl

theorem duplicate_claim_rejected
    (s : RewardState) (c : RewardClaim) :
    ¬ claimUnique (processRewardClaim s c) c.nonce := by
  intro hUnique
  exact hUnique (Finset.mem_union_right _ (Finset.mem_singleton_self c.nonce))

theorem reward_budget_bounded
    (s : RewardState) (c : RewardClaim)
    (_hPositive : 0 < c.rewardAmount)
    (hBudget : s.totalPaid + c.rewardAmount ≤ s.totalBudget) :
    (processRewardClaim s c).totalPaid ≤ s.totalBudget := by
  simpa [processRewardClaim] using hBudget

/-! ## Settlement and CPMM safety -/

structure SettlementBatch where
  deltas : List Int
  fees : Int
  treasuryFlow : Int
  burnFlow : Int
  rewardFlow : Int
  rebateFlow : Int

def SettlementBatch.conserved (b : SettlementBatch) : Prop :=
  b.deltas.sum +
    b.fees +
    b.treasuryFlow +
    b.burnFlow +
    b.rewardFlow +
    b.rebateFlow = 0

theorem settlement_composition_conserved
    (b1 b2 : SettlementBatch)
    (h1 : b1.conserved) (h2 : b2.conserved) :
    (b1.deltas ++ b2.deltas).sum +
      (b1.fees + b2.fees) +
      (b1.treasuryFlow + b2.treasuryFlow) +
      (b1.burnFlow + b2.burnFlow) +
      (b1.rewardFlow + b2.rewardFlow) +
      (b1.rebateFlow + b2.rebateFlow) = 0 := by
  rw [List.sum_append]
  unfold SettlementBatch.conserved at h1 h2
  omega

def cpmmExactInOutput (reserveIn reserveOut amountIn : Nat) : Nat :=
  if reserveIn + amountIn = 0 then 0
  else reserveOut * amountIn / (reserveIn + amountIn)

theorem cpmm_output_le_reserve
    (reserveIn reserveOut amountIn : Nat) :
    cpmmExactInOutput reserveIn reserveOut amountIn ≤ reserveOut := by
  unfold cpmmExactInOutput
  split_ifs
  · omega
  · exact Nat.div_le_of_le_mul (by nlinarith)

/-! ## Disaster coverage monotonicity -/

def residualRisk {Axis Trace : Type*}
    (activeAxes : Set Axis) (traces : Set Trace)
    (covers : Axis -> Trace -> Prop) : Set Trace :=
  {trace ∈ traces | ¬ ∃ axis ∈ activeAxes, covers axis trace}

def fullCoverage {Axis Trace : Type*}
    (activeAxes : Set Axis) (traces : Set Trace)
    (covers : Axis -> Trace -> Prop) : Prop :=
  residualRisk activeAxes traces covers = ∅

theorem adding_axis_reduces_risk {Axis Trace : Type*}
    (activeAxes : Set Axis) (traces : Set Trace)
    (covers : Axis -> Trace -> Prop) (newAxis : Axis) :
    residualRisk (activeAxes ∪ {newAxis}) traces covers ⊆
      residualRisk activeAxes traces covers := by
  intro trace hResidual
  exact ⟨hResidual.1,
    by
      rintro ⟨axis, hAxis, hCovers⟩
      exact hResidual.2
        ⟨axis, Set.mem_union_left {newAxis} hAxis, hCovers⟩⟩

theorem full_coverage_iff {Axis Trace : Type*}
    (activeAxes : Set Axis) (traces : Set Trace)
    (covers : Axis -> Trace -> Prop) :
    fullCoverage activeAxes traces covers ↔
      ∀ trace ∈ traces, ∃ axis ∈ activeAxes, covers axis trace := by
  constructor
  · intro hFull trace hTrace
    by_contra hMissing
    have hResidual :
        trace ∈ residualRisk activeAxes traces covers := by
      exact ⟨hTrace, hMissing⟩
    have hEmpty : trace ∈ (∅ : Set Trace) := by
      unfold fullCoverage at hFull
      rwa [hFull] at hResidual
    exact hEmpty
  · intro hCovered
    unfold fullCoverage
    ext trace
    constructor
    · intro hResidual
      exact False.elim (hResidual.2 (hCovered trace hResidual.1))
    · intro hEmpty
      cases hEmpty

/-! ## Backend-neutral admission bits -/

structure BackendResult where
  proofOk : Bool
  bindingOk : Bool
  policyOk : Bool
  freshnessOk : Bool
  sandboxOk : Bool
  codeIdentityOk : Bool
  deterministicOk : Bool
  deriving DecidableEq, Repr

def backendContextOk (b : BackendResult) : Bool :=
  b.proofOk &&
    b.bindingOk &&
    b.policyOk &&
    b.freshnessOk &&
    b.sandboxOk &&
    b.codeIdentityOk &&
    b.deterministicOk

def samePublicResult (a b : BackendResult) : Prop :=
  a.proofOk = b.proofOk ∧
    a.bindingOk = b.bindingOk ∧
    a.policyOk = b.policyOk ∧
    a.freshnessOk = b.freshnessOk ∧
    a.sandboxOk = b.sandboxOk ∧
    a.codeIdentityOk = b.codeIdentityOk ∧
    a.deterministicOk = b.deterministicOk

theorem same_public_result_context_ok_eq
    (a b : BackendResult)
    (hSame : samePublicResult a b) :
    backendContextOk a = backendContextOk b := by
  cases a
  cases b
  simp [samePublicResult, backendContextOk] at hSame ⊢
  simp [hSame.1, hSame.2.1, hSame.2.2.1, hSame.2.2.2.1,
    hSame.2.2.2.2.1, hSame.2.2.2.2.2.1, hSame.2.2.2.2.2.2]

theorem code_identity_fail_rejects
    (b : BackendResult)
    (hFail : b.codeIdentityOk = false) :
    backendContextOk b = false := by
  simp [backendContextOk, hFail]

theorem sandbox_fail_rejects
    (b : BackendResult)
    (hFail : b.sandboxOk = false) :
    backendContextOk b = false := by
  simp [backendContextOk, hFail]

theorem deterministic_fail_rejects
    (b : BackendResult)
    (hFail : b.deterministicOk = false) :
    backendContextOk b = false := by
  simp [backendContextOk, hFail]

end ZenoDEXAristotleDisasterBasis
end Proofs
