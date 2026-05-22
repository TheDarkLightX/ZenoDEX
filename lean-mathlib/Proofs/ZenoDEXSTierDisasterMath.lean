import Mathlib

/-!
# ZenoDEX S-tier Disaster Math

This file promotes the latest Aristotle S-tier disaster-state packet into the
public Lean tree under the repo toolchain.

The theorems are compact gate laws. They prove source-bounded payout,
reserve-first outflow, canonical work deduplication, oracle-bridge preservation,
and code-signing revocation behavior. They do not prove legal compliance,
cryptographic soundness, oracle truth, runtime liveness, or backend refinement.
-/

namespace Proofs
namespace ZenoDEXSTierDisasterMath

/-! ## Funding source and waterfall core -/

structure SourceGate where
  sourceVerified : Bool
  noProfitRight : Bool
  noPassiveYield : Bool
  noFutureEntrant : Bool
  disclosureMet : Bool
  isSensitive : Bool
  legalCapability : Bool

def SourceGate.admitted (s : SourceGate) : Prop :=
  s.sourceVerified = true ∧
    s.noProfitRight = true ∧
    s.noPassiveYield = true ∧
    s.noFutureEntrant = true ∧
    s.disclosureMet = true ∧
    (s.isSensitive = true → s.legalCapability = true)

structure WaterfallCert where
  realizedSurplus : Nat
  reserveTopup : Nat
  derivativePayout : Nat
  burn : Nat
  workBudget : Nat
  residual : Nat
  reserveDeficit : Nat
  balance :
    reserveTopup + derivativePayout + burn + workBudget + residual = realizedSurplus
  reserveFirst :
    reserveTopup < reserveDeficit →
      burn = 0 ∧ workBudget = 0 ∧ derivativePayout = 0 ∧ residual = 0

structure CapMeetCert where
  payment : Nat
  verifiedValue : Nat
  workBudgetCap : Nat
  treasuryCap : Nat
  sybilCap : Nat
  scopeCap : Nat
  hVerified : payment ≤ verifiedValue
  hWork : payment ≤ workBudgetCap
  hTreasury : payment ≤ treasuryCap
  hSybil : payment ≤ sybilCap
  hScope : payment ≤ scopeCap

theorem counterexample_original_target1 :
    ∃ (src : SourceGate) (w : WaterfallCert) (cap : CapMeetCert),
      src.admitted ∧ cap.workBudgetCap ≤ w.workBudget ∧ cap.payment > 0 ∧
      ¬ (src.noPassiveYield = false ∧ src.noFutureEntrant = false) := by
  refine ⟨⟨true, true, true, true, true, true, true⟩,
    ⟨1, 0, 0, 0, 1, 0, 0, by norm_num, ?_⟩,
    ⟨1, 1, 1, 1, 1, 1,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    ?_⟩
  · intro h
    omega
  · simp [SourceGate.admitted]

theorem admitted_source_blocks_bad_funding
    (src : SourceGate) (hSrc : src.admitted) :
    src.noPassiveYield = true ∧ src.noFutureEntrant = true :=
  ⟨hSrc.2.2.1, hSrc.2.2.2.1⟩

theorem passive_or_future_source_not_admitted
    (src : SourceGate)
    (hBad : src.noPassiveYield = false ∨ src.noFutureEntrant = false) :
    ¬ src.admitted := by
  intro hSrc
  rcases hBad with hPassive | hFuture
  · rw [hSrc.2.2.1] at hPassive
    contradiction
  · rw [hSrc.2.2.2.1] at hFuture
    contradiction

theorem positive_payout_implies_reserve_source_and_surplus_bound
    (src : SourceGate) (w : WaterfallCert) (cap : CapMeetCert)
    (hSrc : src.admitted)
    (hLink : cap.workBudgetCap ≤ w.workBudget)
    (hPay : cap.payment > 0) :
    w.reserveTopup ≥ w.reserveDeficit ∧
      cap.payment ≤ w.realizedSurplus ∧
      src.noPassiveYield = true ∧
      src.noFutureEntrant = true := by
  have hReserve : w.reserveTopup ≥ w.reserveDeficit := by
    by_contra hNot
    have hLt : w.reserveTopup < w.reserveDeficit := Nat.lt_of_not_ge hNot
    have hWorkZero : w.workBudget = 0 := (w.reserveFirst hLt).2.1
    have hPaymentZero : cap.payment = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact le_trans cap.hWork (le_trans hLink (by omega))
    omega
  have hWorkLeSurplus : w.workBudget ≤ w.realizedSurplus := by
    have hBal := w.balance
    omega
  exact ⟨hReserve, le_trans cap.hWork (le_trans hLink hWorkLeSurplus),
    hSrc.2.2.1, hSrc.2.2.2.1⟩

theorem zero_surplus_forces_zero_outflow
    (w : WaterfallCert) (cap : CapMeetCert)
    (hLink : cap.workBudgetCap ≤ w.workBudget)
    (hZero : w.realizedSurplus = 0) :
    w.burn = 0 ∧ w.workBudget = 0 ∧ cap.payment = 0 := by
  have hBal := w.balance
  have hBurnZero : w.burn = 0 := by omega
  have hWorkZero : w.workBudget = 0 := by omega
  have hPayZero : cap.payment = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact le_trans cap.hWork (le_trans hLink (by omega))
  exact ⟨hBurnZero, hWorkZero, hPayZero⟩

/-! ## Receipt, consumed-set, and normalized work identity -/

structure WorkReceipt where
  canonicalId : Nat
  hasProof : Bool
  hasScope : Bool
  antiSybil : Bool
  quorumMet : Bool
  auxData : Nat
  deriving DecidableEq

def WorkReceipt.accepted (r : WorkReceipt) : Prop :=
  r.hasProof = true ∧ r.hasScope = true ∧ r.antiSybil = true ∧ r.quorumMet = true

def processClaim (claimId : Nat) (consumed : Finset Nat) : Bool × Finset Nat :=
  if claimId ∈ consumed then
    (false, consumed)
  else
    (true, consumed ∪ {claimId})

structure Artifact where
  statementRoot : Nat
  assumptionRoot : Nat
  inputRoot : Nat
  outputRoot : Nat
  publicResultRoot : Nat
  claimId : Nat
  nonce : Nat
  epoch : Nat
  deriving DecidableEq

def sameWork (a b : Artifact) : Prop :=
  a.statementRoot = b.statementRoot ∧
    a.assumptionRoot = b.assumptionRoot ∧
    a.inputRoot = b.inputRoot ∧
    a.outputRoot = b.outputRoot ∧
    a.publicResultRoot = b.publicResultRoot

def processWork (canon : Artifact → Nat) (a : Artifact) (paid : Finset Nat) :
    Bool × Finset Nat :=
  processClaim (canon a) paid

theorem same_work_pay_once_under_canonicalizer
    (canon : Artifact → Nat)
    (hCanon : ∀ a b, sameWork a b → canon a = canon b)
    (paid : Finset Nat) (a b : Artifact)
    (hFresh : canon a ∉ paid)
    (hSame : sameWork a b) :
    (processWork canon b (processWork canon a paid).2).1 = false := by
  have hEq : canon b = canon a := (hCanon a b hSame).symm
  have hMem : canon b ∈ paid ∪ {canon a} := by
    rw [hEq]
    exact Finset.mem_union_right paid (Finset.mem_singleton_self (canon a))
  have hCond : canon b = canon a ∨ canon b ∈ paid := Or.inl hEq
  simp [processWork, processClaim, hFresh, hCond]

theorem raw_inequality_is_not_work_uniqueness :
    ∃ a b : Artifact, a ≠ b ∧ sameWork a b := by
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨0, 0, 0, 0, 0, 0, 1, 0⟩, ?_, ?_⟩
  · decide
  · simp [sameWork]

/-! ## ZenoOracle bridge and proof result preservation -/

structure ProofResult where
  claimId : Nat
  publicResultRoot : Nat
  epoch : Nat
  verified : Bool
  deriving DecidableEq

structure OracleReceipt where
  claimId : Nat
  publicResultRoot : Nat
  oracleWindow : Nat
  consumerAction : Nat
  epoch : Nat
  deriving DecidableEq

structure BridgeAdmission where
  result : ProofResult
  receipt : OracleReceipt
  expectedConsumer : Nat
  freshWindow : Nat
  claimPreserved : receipt.claimId = result.claimId
  resultPreserved : receipt.publicResultRoot = result.publicResultRoot
  consumerPreserved : receipt.consumerAction = expectedConsumer
  freshness : result.epoch ≤ receipt.epoch ∧ receipt.epoch - result.epoch ≤ freshWindow
  verified : result.verified = true

theorem bridge_admission_exposes_all_settlement_gates
    (ba : BridgeAdmission) :
    ba.receipt.claimId = ba.result.claimId ∧
      ba.receipt.publicResultRoot = ba.result.publicResultRoot ∧
      ba.receipt.consumerAction = ba.expectedConsumer ∧
      ba.result.epoch ≤ ba.receipt.epoch ∧
      ba.receipt.epoch - ba.result.epoch ≤ ba.freshWindow ∧
      ba.result.verified = true :=
  ⟨ba.claimPreserved, ba.resultPreserved, ba.consumerPreserved,
    ba.freshness.1, ba.freshness.2, ba.verified⟩

/-! ## Code-signing identity gate -/

structure CodeSigningRecord where
  verifierId : Nat
  binaryDigest : Nat
  toolchainId : Nat
  releaseKey : Nat
  signature : Nat
  revoked : Bool
  deriving DecidableEq

def codeSigningAdmitted (rec : CodeSigningRecord)
    (allowedVerifier allowedDigest allowedToolchain allowedKey : Nat → Prop)
    (signatureValid : CodeSigningRecord → Prop) : Prop :=
  allowedVerifier rec.verifierId ∧
    allowedDigest rec.binaryDigest ∧
    allowedToolchain rec.toolchainId ∧
    allowedKey rec.releaseKey ∧
    signatureValid rec ∧
    rec.revoked = false

theorem revoked_code_signing_record_not_admitted
    (rec : CodeSigningRecord)
    (allowedVerifier allowedDigest allowedToolchain allowedKey : Nat → Prop)
    (signatureValid : CodeSigningRecord → Prop)
    (hRevoked : rec.revoked = true) :
    ¬ codeSigningAdmitted rec allowedVerifier allowedDigest allowedToolchain
        allowedKey signatureValid := by
  intro h
  unfold codeSigningAdmitted at h
  rw [hRevoked] at h
  exact Bool.noConfusion h.2.2.2.2.2

end ZenoDEXSTierDisasterMath
end Proofs
