/-!
# ZenoDEX Settlement Replay Context

This file models the replay-context commitment added to the runtime settlement
certificate path.

The runtime object stores the replay inputs directly:

- intent commitment
- settlement commitment
- pre-state root
- pre-support root
- post-state root
- post-support root
- a commitment over those fields

The theorem layer proves the structural property we need from that shape:
when a certificate verifies with a replay context, the certificate is bound to
the exact replay inputs it claims.  A stale pre-state, changed intent set, or
different post-state cannot satisfy the same required replay-context predicate.

This is an abstract model of commitment binding.  It does not claim SHA-256
collision resistance, Python serialization correctness, or equality with the
runtime byte encoding.  Those remain runtime bridge and cryptographic
assumptions.
-/

namespace TauSwap
namespace ZenoDEX
namespace SettlementReplayContext

abbrev Hash := Nat

structure ReplayContextInputs where
  intentCommitment : Hash
  settlementCommitment : Hash
  preStateRoot : Hash
  preSupportRoot : Hash
  postStateRoot : Hash
  postSupportRoot : Hash
  deriving DecidableEq, Repr

structure ReplayContextCommitment where
  intentCommitment : Hash
  settlementCommitment : Hash
  preStateRoot : Hash
  preSupportRoot : Hash
  postStateRoot : Hash
  postSupportRoot : Hash
  replayContextCommitment : Hash
  deriving DecidableEq, Repr

def replayContextDigest (inputs : ReplayContextInputs) : Hash :=
  inputs.intentCommitment +
    inputs.settlementCommitment +
    inputs.preStateRoot +
    inputs.preSupportRoot +
    inputs.postStateRoot +
    inputs.postSupportRoot

def buildReplayContext (inputs : ReplayContextInputs) : ReplayContextCommitment :=
  {
    intentCommitment := inputs.intentCommitment
    settlementCommitment := inputs.settlementCommitment
    preStateRoot := inputs.preStateRoot
    preSupportRoot := inputs.preSupportRoot
    postStateRoot := inputs.postStateRoot
    postSupportRoot := inputs.postSupportRoot
    replayContextCommitment := replayContextDigest inputs
  }

def VerifyReplayContext
    (inputs : ReplayContextInputs)
    (commitment : ReplayContextCommitment) : Prop :=
  commitment = buildReplayContext inputs

structure StrongCertificate where
  settlementCommitment : Hash
  deltaCommitment : Hash
  replayContext : Option ReplayContextCommitment
  deriving DecidableEq, Repr

def VerifyStrongCertificate
    (inputs : ReplayContextInputs)
    (certificate : StrongCertificate) : Prop :=
  certificate.settlementCommitment = inputs.settlementCommitment ∧
    match certificate.replayContext with
    | none => True
    | some context =>
        VerifyReplayContext inputs context ∧
          context.settlementCommitment = certificate.settlementCommitment

def RequiredReplayContextOK
    (inputs : ReplayContextInputs)
    (certificate : StrongCertificate) : Prop :=
  ∃ context,
    certificate.replayContext = some context ∧
      VerifyStrongCertificate inputs certificate

theorem verifyReplayContext_intentCommitment
    {inputs : ReplayContextInputs}
    {commitment : ReplayContextCommitment}
    (h : VerifyReplayContext inputs commitment) :
    commitment.intentCommitment = inputs.intentCommitment := by
  cases h
  rfl

theorem verifyReplayContext_settlementCommitment
    {inputs : ReplayContextInputs}
    {commitment : ReplayContextCommitment}
    (h : VerifyReplayContext inputs commitment) :
    commitment.settlementCommitment = inputs.settlementCommitment := by
  cases h
  rfl

theorem verifyReplayContext_preStateRoot
    {inputs : ReplayContextInputs}
    {commitment : ReplayContextCommitment}
    (h : VerifyReplayContext inputs commitment) :
    commitment.preStateRoot = inputs.preStateRoot := by
  cases h
  rfl

theorem verifyReplayContext_preSupportRoot
    {inputs : ReplayContextInputs}
    {commitment : ReplayContextCommitment}
    (h : VerifyReplayContext inputs commitment) :
    commitment.preSupportRoot = inputs.preSupportRoot := by
  cases h
  rfl

theorem verifyReplayContext_postStateRoot
    {inputs : ReplayContextInputs}
    {commitment : ReplayContextCommitment}
    (h : VerifyReplayContext inputs commitment) :
    commitment.postStateRoot = inputs.postStateRoot := by
  cases h
  rfl

theorem verifyReplayContext_postSupportRoot
    {inputs : ReplayContextInputs}
    {commitment : ReplayContextCommitment}
    (h : VerifyReplayContext inputs commitment) :
    commitment.postSupportRoot = inputs.postSupportRoot := by
  cases h
  rfl

theorem verifyReplayContext_inputs_unique
    {left right : ReplayContextInputs}
    {commitment : ReplayContextCommitment}
    (hLeft : VerifyReplayContext left commitment)
    (hRight : VerifyReplayContext right commitment) :
    left = right := by
  cases left
  cases right
  unfold VerifyReplayContext buildReplayContext at hLeft hRight
  subst commitment
  cases hRight
  rfl

theorem verifyStrongCertificate_with_context_binds_settlement
    {inputs : ReplayContextInputs}
    {certificate : StrongCertificate}
    {context : ReplayContextCommitment}
    (hVerify : VerifyStrongCertificate inputs certificate)
    (hContext : certificate.replayContext = some context) :
    context.settlementCommitment = certificate.settlementCommitment := by
  unfold VerifyStrongCertificate at hVerify
  cases hVerify with
  | intro _ hReplay =>
      rw [hContext] at hReplay
      exact hReplay.2

theorem verifyStrongCertificate_with_context_binds_preStateRoot
    {inputs : ReplayContextInputs}
    {certificate : StrongCertificate}
    {context : ReplayContextCommitment}
    (hVerify : VerifyStrongCertificate inputs certificate)
    (hContext : certificate.replayContext = some context) :
    context.preStateRoot = inputs.preStateRoot := by
  unfold VerifyStrongCertificate at hVerify
  cases hVerify with
  | intro _ hReplay =>
      rw [hContext] at hReplay
      exact verifyReplayContext_preStateRoot hReplay.1

theorem verifyStrongCertificate_with_context_binds_postStateRoot
    {inputs : ReplayContextInputs}
    {certificate : StrongCertificate}
    {context : ReplayContextCommitment}
    (hVerify : VerifyStrongCertificate inputs certificate)
    (hContext : certificate.replayContext = some context) :
    context.postStateRoot = inputs.postStateRoot := by
  unfold VerifyStrongCertificate at hVerify
  cases hVerify with
  | intro _ hReplay =>
      rw [hContext] at hReplay
      exact verifyReplayContext_postStateRoot hReplay.1

theorem requiredReplayContext_inputs_unique
    {left right : ReplayContextInputs}
    {certificate : StrongCertificate}
    (hLeft : RequiredReplayContextOK left certificate)
    (hRight : RequiredReplayContextOK right certificate) :
    left = right := by
  rcases hLeft with ⟨leftContext, hLeftContext, hLeftVerify⟩
  rcases hRight with ⟨rightContext, hRightContext, hRightVerify⟩
  have hContexts : leftContext = rightContext := by
    rw [hLeftContext] at hRightContext
    cases hRightContext
    rfl
  unfold VerifyStrongCertificate at hLeftVerify hRightVerify
  cases hLeftVerify with
  | intro _ hLeftReplay =>
      cases hRightVerify with
      | intro _ hRightReplay =>
          rw [hLeftContext] at hLeftReplay
          rw [hRightContext] at hRightReplay
          rw [← hContexts] at hRightReplay
          exact verifyReplayContext_inputs_unique hLeftReplay.1 hRightReplay.1

theorem requiredReplayContext_preStateRoot_unique
    {left right : ReplayContextInputs}
    {certificate : StrongCertificate}
    (hLeft : RequiredReplayContextOK left certificate)
    (hRight : RequiredReplayContextOK right certificate) :
    left.preStateRoot = right.preStateRoot := by
  have hInputs : left = right :=
    requiredReplayContext_inputs_unique hLeft hRight
  rw [hInputs]

theorem requiredReplayContext_postStateRoot_unique
    {left right : ReplayContextInputs}
    {certificate : StrongCertificate}
    (hLeft : RequiredReplayContextOK left certificate)
    (hRight : RequiredReplayContextOK right certificate) :
    left.postStateRoot = right.postStateRoot := by
  have hInputs : left = right :=
    requiredReplayContext_inputs_unique hLeft hRight
  rw [hInputs]

end SettlementReplayContext
end ZenoDEX
end TauSwap
