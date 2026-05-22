namespace ZenoDEX

inductive IntentRejectReason where
  | invalidSignature
  | nonceInvalid
  | other
  deriving DecidableEq, Repr

structure IntentAuthShape where
  signer : Nat
  declaredSender : Nat
  nonce : Nat
  signaturePresent : Bool
  signatureVerifies : Bool

structure IntentAdmissionResult where
  ok : Bool
  reason : Option IntentRejectReason
  nonceConsumed : Bool
  stateExposed : Bool
  settlementExposed : Bool

def verifyIntentSenderBoundary (a : IntentAuthShape) : Bool :=
  a.signaturePresent && a.signatureVerifies && (a.signer == a.declaredSender)

def admitSignedIntentBoundary (a : IntentAuthShape) : IntentAdmissionResult :=
  if verifyIntentSenderBoundary a then
    {
      ok := true,
      reason := none,
      nonceConsumed := true,
      stateExposed := true,
      settlementExposed := true
    }
  else
    {
      ok := false,
      reason := some IntentRejectReason.invalidSignature,
      nonceConsumed := false,
      stateExposed := false,
      settlementExposed := false
    }

theorem sender_boundary_replay_rejects_before_nonce
    (a : IntentAuthShape)
    (hSignerChanged : a.signer != a.declaredSender) :
    admitSignedIntentBoundary a =
      {
        ok := false,
        reason := some IntentRejectReason.invalidSignature,
        nonceConsumed := false,
        stateExposed := false,
        settlementExposed := false
      } := by
  unfold admitSignedIntentBoundary verifyIntentSenderBoundary
  simp [Bool.and_eq_true, beq_iff_eq]
  intro _ _ h
  simp [h] at hSignerChanged

theorem sender_boundary_replay_does_not_expose_state
    (a : IntentAuthShape)
    (hSignerChanged : a.signer != a.declaredSender) :
    (admitSignedIntentBoundary a).stateExposed = false ∧
      (admitSignedIntentBoundary a).settlementExposed = false ∧
      (admitSignedIntentBoundary a).nonceConsumed = false := by
  have h := sender_boundary_replay_rejects_before_nonce a hSignerChanged
  simp [h]

end ZenoDEX
