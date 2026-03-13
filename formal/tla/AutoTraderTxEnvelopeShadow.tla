---- MODULE AutoTraderTxEnvelopeShadow ----

(*
Independent shadow semantics for the live autotrader Tau transaction envelope.

This model captures the intended policy meaning, not Tau syntax:
- idle steps are admissible,
- requested transactions require paired sequence/expiration arguments,
- requested transactions require validated bounds,
- requested transactions must carry only the allowed stream scope.
*)

VARIABLES
  txRequested,
  sequencePresent,
  expirationPresent,
  sequenceValid,
  expirationValid,
  feeLimitValid,
  intentStreamPresent,
  settlementStreamAbsent,
  extraCustomStreamsAbsent,
  accepted,
  lastAction

TypeOK ==
  /\ txRequested \in BOOLEAN
  /\ sequencePresent \in BOOLEAN
  /\ expirationPresent \in BOOLEAN
  /\ sequenceValid \in BOOLEAN
  /\ expirationValid \in BOOLEAN
  /\ feeLimitValid \in BOOLEAN
  /\ intentStreamPresent \in BOOLEAN
  /\ settlementStreamAbsent \in BOOLEAN
  /\ extraCustomStreamsAbsent \in BOOLEAN
  /\ accepted \in BOOLEAN
  /\ lastAction \in {
       "init",
       "idle",
       "accept_requested",
       "reject_missing_args",
       "reject_bad_bounds",
       "reject_bad_stream_scope"
     }

RequestedArgsPaired ==
  sequencePresent /\ expirationPresent

RequestedBoundsValid ==
  sequenceValid /\ expirationValid /\ feeLimitValid

RequestedStreamScopeValid ==
  intentStreamPresent /\ settlementStreamAbsent /\ extraCustomStreamsAbsent

RequestedEnvelopeValid ==
  RequestedArgsPaired /\ RequestedBoundsValid /\ RequestedStreamScopeValid

Init ==
  /\ txRequested = FALSE
  /\ sequencePresent = FALSE
  /\ expirationPresent = FALSE
  /\ sequenceValid = FALSE
  /\ expirationValid = FALSE
  /\ feeLimitValid = FALSE
  /\ intentStreamPresent = FALSE
  /\ settlementStreamAbsent = FALSE
  /\ extraCustomStreamsAbsent = FALSE
  /\ accepted = TRUE
  /\ lastAction = "init"

Idle ==
  /\ txRequested' = FALSE
  /\ sequencePresent' = FALSE
  /\ expirationPresent' = FALSE
  /\ sequenceValid' = FALSE
  /\ expirationValid' = FALSE
  /\ feeLimitValid' = FALSE
  /\ intentStreamPresent' = FALSE
  /\ settlementStreamAbsent' = FALSE
  /\ extraCustomStreamsAbsent' = FALSE
  /\ accepted' = TRUE
  /\ lastAction' = "idle"

AcceptRequested ==
  /\ txRequested' = TRUE
  /\ sequencePresent' = TRUE
  /\ expirationPresent' = TRUE
  /\ sequenceValid' = TRUE
  /\ expirationValid' = TRUE
  /\ feeLimitValid' = TRUE
  /\ intentStreamPresent' = TRUE
  /\ settlementStreamAbsent' = TRUE
  /\ extraCustomStreamsAbsent' = TRUE
  /\ accepted' = TRUE
  /\ lastAction' = "accept_requested"

RejectMissingArgs ==
  /\ txRequested' = TRUE
  /\ sequencePresent' = TRUE
  /\ expirationPresent' = FALSE
  /\ sequenceValid' = TRUE
  /\ expirationValid' = TRUE
  /\ feeLimitValid' = TRUE
  /\ intentStreamPresent' = TRUE
  /\ settlementStreamAbsent' = TRUE
  /\ extraCustomStreamsAbsent' = TRUE
  /\ accepted' = FALSE
  /\ lastAction' = "reject_missing_args"

RejectBadBounds ==
  /\ txRequested' = TRUE
  /\ sequencePresent' = TRUE
  /\ expirationPresent' = TRUE
  /\ sequenceValid' = TRUE
  /\ expirationValid' = TRUE
  /\ feeLimitValid' = FALSE
  /\ intentStreamPresent' = TRUE
  /\ settlementStreamAbsent' = TRUE
  /\ extraCustomStreamsAbsent' = TRUE
  /\ accepted' = FALSE
  /\ lastAction' = "reject_bad_bounds"

RejectBadStreamScope ==
  /\ txRequested' = TRUE
  /\ sequencePresent' = TRUE
  /\ expirationPresent' = TRUE
  /\ sequenceValid' = TRUE
  /\ expirationValid' = TRUE
  /\ feeLimitValid' = TRUE
  /\ intentStreamPresent' = TRUE
  /\ settlementStreamAbsent' = FALSE
  /\ extraCustomStreamsAbsent' = TRUE
  /\ accepted' = FALSE
  /\ lastAction' = "reject_bad_stream_scope"

Next ==
  Idle
  \/ AcceptRequested
  \/ RejectMissingArgs
  \/ RejectBadBounds
  \/ RejectBadStreamScope

Spec ==
  Init /\ [][Next]_<<
    txRequested,
    sequencePresent,
    expirationPresent,
    sequenceValid,
    expirationValid,
    feeLimitValid,
    intentStreamPresent,
    settlementStreamAbsent,
    extraCustomStreamsAbsent,
    accepted,
    lastAction
  >>

IdleAlwaysAccepted ==
  ~txRequested => accepted

AcceptedOnlyWhenRequestedEnvelopeValid ==
  txRequested => (accepted <=> RequestedEnvelopeValid)

RejectedRequestedTxHasSpecificReason ==
  (txRequested /\ ~accepted)
    => lastAction \in {"reject_missing_args", "reject_bad_bounds", "reject_bad_stream_scope"}

====
