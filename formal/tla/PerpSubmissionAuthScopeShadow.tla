---- MODULE PerpSubmissionAuthScopeShadow ----

(*
Independent shadow semantics for the modeled perps submission auth lane.

This model captures the key admission contract:
- exactly one auth mode must be selected,
- accepted signed-mode submissions require all signed checks,
- sender-bound mode never consumes a nonce,
- nonce consumption only happens for accepted signed-mode submissions.
*)

VARIABLES
  signedMode,
  senderBoundMode,
  signedSurfaceOk,
  signerRoleOk,
  deadlineOk,
  nonceDomainOk,
  nonceExpectedOk,
  signatureOk,
  senderBindingOk,
  admissionOk,
  consumeNonce,
  lastAction

TypeOK ==
  /\ signedMode \in BOOLEAN
  /\ senderBoundMode \in BOOLEAN
  /\ signedSurfaceOk \in BOOLEAN
  /\ signerRoleOk \in BOOLEAN
  /\ deadlineOk \in BOOLEAN
  /\ nonceDomainOk \in BOOLEAN
  /\ nonceExpectedOk \in BOOLEAN
  /\ signatureOk \in BOOLEAN
  /\ senderBindingOk \in BOOLEAN
  /\ admissionOk \in BOOLEAN
  /\ consumeNonce \in BOOLEAN
  /\ lastAction \in {
       "init",
       "accept_signed",
       "reject_invalid_mode",
       "reject_expired_deadline",
       "reject_sender_binding"
     }

ExactlyOneMode ==
  (signedMode /\ ~senderBoundMode) \/ (~signedMode /\ senderBoundMode)

Init ==
  /\ signedMode = FALSE
  /\ senderBoundMode = FALSE
  /\ signedSurfaceOk = FALSE
  /\ signerRoleOk = FALSE
  /\ deadlineOk = FALSE
  /\ nonceDomainOk = FALSE
  /\ nonceExpectedOk = FALSE
  /\ signatureOk = FALSE
  /\ senderBindingOk = FALSE
  /\ admissionOk = FALSE
  /\ consumeNonce = FALSE
  /\ lastAction = "init"

AcceptSigned ==
  /\ signedMode' = TRUE
  /\ senderBoundMode' = FALSE
  /\ signedSurfaceOk' = TRUE
  /\ signerRoleOk' = TRUE
  /\ deadlineOk' = TRUE
  /\ nonceDomainOk' = TRUE
  /\ nonceExpectedOk' = TRUE
  /\ signatureOk' = TRUE
  /\ senderBindingOk' = TRUE
  /\ admissionOk' = TRUE
  /\ consumeNonce' = TRUE
  /\ lastAction' = "accept_signed"

RejectInvalidMode ==
  /\ signedMode' = TRUE
  /\ senderBoundMode' = TRUE
  /\ signedSurfaceOk' = TRUE
  /\ signerRoleOk' = TRUE
  /\ deadlineOk' = TRUE
  /\ nonceDomainOk' = TRUE
  /\ nonceExpectedOk' = TRUE
  /\ signatureOk' = TRUE
  /\ senderBindingOk' = TRUE
  /\ admissionOk' = FALSE
  /\ consumeNonce' = FALSE
  /\ lastAction' = "reject_invalid_mode"

RejectExpiredDeadline ==
  /\ signedMode' = TRUE
  /\ senderBoundMode' = FALSE
  /\ signedSurfaceOk' = TRUE
  /\ signerRoleOk' = TRUE
  /\ deadlineOk' = FALSE
  /\ nonceDomainOk' = TRUE
  /\ nonceExpectedOk' = TRUE
  /\ signatureOk' = TRUE
  /\ senderBindingOk' = TRUE
  /\ admissionOk' = FALSE
  /\ consumeNonce' = FALSE
  /\ lastAction' = "reject_expired_deadline"

RejectSenderBinding ==
  /\ signedMode' = FALSE
  /\ senderBoundMode' = TRUE
  /\ signedSurfaceOk' = FALSE
  /\ signerRoleOk' = FALSE
  /\ deadlineOk' = FALSE
  /\ nonceDomainOk' = FALSE
  /\ nonceExpectedOk' = FALSE
  /\ signatureOk' = FALSE
  /\ senderBindingOk' = FALSE
  /\ admissionOk' = FALSE
  /\ consumeNonce' = FALSE
  /\ lastAction' = "reject_sender_binding"

Next ==
  AcceptSigned
  \/ RejectInvalidMode
  \/ RejectExpiredDeadline
  \/ RejectSenderBinding

Spec ==
  Init /\ [][Next]_<<
    signedMode,
    senderBoundMode,
    signedSurfaceOk,
    signerRoleOk,
    deadlineOk,
    nonceDomainOk,
    nonceExpectedOk,
    signatureOk,
    senderBindingOk,
    admissionOk,
    consumeNonce,
    lastAction
  >>

AcceptedRequiresExactlyOneMode ==
  admissionOk => ExactlyOneMode

AcceptedSignedModeRequiresAllSignedChecks ==
  admissionOk =>
    /\ signedMode
    /\ ~senderBoundMode
    /\ signedSurfaceOk
    /\ signerRoleOk
    /\ deadlineOk
    /\ nonceDomainOk
    /\ nonceExpectedOk
    /\ signatureOk

SenderBoundModeNeverConsumesNonce ==
  senderBoundMode => ~consumeNonce

NonceConsumedOnlyForAcceptedSignedMode ==
  consumeNonce =>
    /\ admissionOk
    /\ signedMode
    /\ ~senderBoundMode

SenderBoundAdmissionRequiresBinding ==
  (admissionOk /\ senderBoundMode) => senderBindingOk

====
