---- MODULE OrderIntentCancelExpiryShadow ----
EXTENDS Naturals

(*
Independent shadow semantics for the cancel/expiry order lifecycle.

This model intentionally does not reuse Tau or ESSO syntax. It captures the
intended admission semantics for the modeled order lane:
- cancelling a live order must never emit an executable intent,
- executing an expired order must be rejected without emitting an intent,
- emitted intents only arise from executing a live order inside its validity
  window.
*)

CONSTANT MAX_EPOCH

VARIABLES
  orderStatus,
  prevOrderStatus,
  nowEpoch,
  prevNowEpoch,
  validFromEpoch,
  validUntilEpoch,
  intentEmitted,
  lastAction

Statuses == {"Live", "Cancelled", "Filled"}
Actions ==
  {
    "init",
    "advance_epoch",
    "cancel",
    "execute_allowed",
    "execute_reject_cancelled",
    "execute_reject_expired",
    "noop"
  }

TypeOK ==
  /\ orderStatus \in Statuses
  /\ prevOrderStatus \in Statuses
  /\ nowEpoch \in Nat
  /\ prevNowEpoch \in Nat
  /\ nowEpoch <= MAX_EPOCH
  /\ prevNowEpoch <= MAX_EPOCH
  /\ validFromEpoch \in Nat
  /\ validUntilEpoch \in Nat
  /\ validUntilEpoch <= MAX_EPOCH
  /\ validFromEpoch <= validUntilEpoch
  /\ intentEmitted \in BOOLEAN
  /\ lastAction \in Actions

WithinWindow(epoch) ==
  /\ validFromEpoch <= epoch
  /\ epoch <= validUntilEpoch

Init ==
  /\ orderStatus = "Live"
  /\ prevOrderStatus = "Live"
  /\ nowEpoch = 0
  /\ prevNowEpoch = 0
  /\ validFromEpoch = 0
  /\ validUntilEpoch = 2
  /\ intentEmitted = FALSE
  /\ lastAction = "init"

AdvanceEpoch ==
  /\ nowEpoch < MAX_EPOCH
  /\ prevOrderStatus' = orderStatus
  /\ prevNowEpoch' = nowEpoch
  /\ nowEpoch' = nowEpoch + 1
  /\ orderStatus' = orderStatus
  /\ validFromEpoch' = validFromEpoch
  /\ validUntilEpoch' = validUntilEpoch
  /\ intentEmitted' = FALSE
  /\ lastAction' = "advance_epoch"

Cancel ==
  /\ orderStatus = "Live"
  /\ prevOrderStatus' = orderStatus
  /\ prevNowEpoch' = nowEpoch
  /\ nowEpoch' = nowEpoch
  /\ orderStatus' = "Cancelled"
  /\ validFromEpoch' = validFromEpoch
  /\ validUntilEpoch' = validUntilEpoch
  /\ intentEmitted' = FALSE
  /\ lastAction' = "cancel"

ExecuteAllowed ==
  /\ orderStatus = "Live"
  /\ WithinWindow(nowEpoch)
  /\ prevOrderStatus' = orderStatus
  /\ prevNowEpoch' = nowEpoch
  /\ nowEpoch' = nowEpoch
  /\ orderStatus' = "Filled"
  /\ validFromEpoch' = validFromEpoch
  /\ validUntilEpoch' = validUntilEpoch
  /\ intentEmitted' = TRUE
  /\ lastAction' = "execute_allowed"

ExecuteRejectCancelled ==
  /\ orderStatus = "Cancelled"
  /\ prevOrderStatus' = orderStatus
  /\ prevNowEpoch' = nowEpoch
  /\ nowEpoch' = nowEpoch
  /\ orderStatus' = orderStatus
  /\ validFromEpoch' = validFromEpoch
  /\ validUntilEpoch' = validUntilEpoch
  /\ intentEmitted' = FALSE
  /\ lastAction' = "execute_reject_cancelled"

ExecuteRejectExpired ==
  /\ orderStatus = "Live"
  /\ nowEpoch > validUntilEpoch
  /\ prevOrderStatus' = orderStatus
  /\ prevNowEpoch' = nowEpoch
  /\ nowEpoch' = nowEpoch
  /\ orderStatus' = orderStatus
  /\ validFromEpoch' = validFromEpoch
  /\ validUntilEpoch' = validUntilEpoch
  /\ intentEmitted' = FALSE
  /\ lastAction' = "execute_reject_expired"

NoOp ==
  /\ prevOrderStatus' = prevOrderStatus
  /\ prevNowEpoch' = prevNowEpoch
  /\ nowEpoch' = nowEpoch
  /\ orderStatus' = orderStatus
  /\ validFromEpoch' = validFromEpoch
  /\ validUntilEpoch' = validUntilEpoch
  /\ intentEmitted' = intentEmitted
  /\ lastAction' = lastAction

Next ==
  AdvanceEpoch
  \/ Cancel
  \/ ExecuteAllowed
  \/ ExecuteRejectCancelled
  \/ ExecuteRejectExpired
  \/ NoOp

Spec ==
  Init /\ [][Next]_<<
    orderStatus,
    prevOrderStatus,
    nowEpoch,
    prevNowEpoch,
    validFromEpoch,
    validUntilEpoch,
    intentEmitted,
    lastAction
  >>

CancelledNeverEmitsIntent ==
  (orderStatus = "Cancelled") => ~intentEmitted

CancelledExecutionRejectedWithoutIntent ==
  (lastAction = "execute_reject_cancelled") =>
    /\ prevOrderStatus = "Cancelled"
    /\ orderStatus = "Cancelled"
    /\ ~intentEmitted

ExpiredExecutionRejectedWithoutIntent ==
  (lastAction = "execute_reject_expired") =>
    /\ prevOrderStatus = "Live"
    /\ orderStatus = "Live"
    /\ prevNowEpoch > validUntilEpoch
    /\ ~intentEmitted

EmittedIntentRequiresLiveOrderWithinWindow ==
  intentEmitted =>
    /\ lastAction = "execute_allowed"
    /\ prevOrderStatus = "Live"
    /\ orderStatus = "Filled"
    /\ WithinWindow(prevNowEpoch)

====
