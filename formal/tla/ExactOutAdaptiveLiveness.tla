---- MODULE ExactOutAdaptiveLiveness ----
EXTENDS Integers

(*
Bounded TLA+ model for the exact-out adaptive liveness lane.

Purpose:
- Capture the control sequencing behind the adaptive exact-out path.
- Model cheap-path attempt first, repaired fallback second, and explicit failure if both fail.
- Check that a pending request never remains unresolved on the modeled control path.

This is intentionally abstract:
- no pool arithmetic or route keys,
- no exact-out candidate generation,
- only adaptive branch order and total outcome resolution.
*)

VARIABLES
  requestPending,
  cheapCanSucceed,
  fallbackCanSucceed,
  cheapAttempted,
  cheapSucceeded,
  fallbackRequired,
  fallbackAttempted,
  fallbackSucceeded,
  returnedSuccess,
  explicitFailure,
  failureReasonPresent

Resolved ==
  returnedSuccess \/ explicitFailure

TypeOK ==
  /\ requestPending \in BOOLEAN
  /\ cheapCanSucceed \in BOOLEAN
  /\ fallbackCanSucceed \in BOOLEAN
  /\ cheapAttempted \in BOOLEAN
  /\ cheapSucceeded \in BOOLEAN
  /\ fallbackRequired \in BOOLEAN
  /\ fallbackAttempted \in BOOLEAN
  /\ fallbackSucceeded \in BOOLEAN
  /\ returnedSuccess \in BOOLEAN
  /\ explicitFailure \in BOOLEAN
  /\ failureReasonPresent \in BOOLEAN

BranchCoherent ==
  /\ cheapSucceeded => cheapAttempted
  /\ fallbackRequired => cheapAttempted /\ ~cheapSucceeded
  /\ fallbackAttempted => fallbackRequired
  /\ fallbackSucceeded => fallbackAttempted
  /\ ~(returnedSuccess /\ explicitFailure)
  /\ explicitFailure => failureReasonPresent
  /\ Resolved => ~requestPending

Init ==
  /\ requestPending = TRUE
  /\ cheapCanSucceed \in BOOLEAN
  /\ fallbackCanSucceed \in BOOLEAN
  /\ cheapAttempted = FALSE
  /\ cheapSucceeded = FALSE
  /\ fallbackRequired = FALSE
  /\ fallbackAttempted = FALSE
  /\ fallbackSucceeded = FALSE
  /\ returnedSuccess = FALSE
  /\ explicitFailure = FALSE
  /\ failureReasonPresent = FALSE

AttemptCheapSuccess ==
  /\ requestPending
  /\ ~cheapAttempted
  /\ cheapCanSucceed
  /\ cheapAttempted' = TRUE
  /\ cheapSucceeded' = TRUE
  /\ fallbackRequired' = FALSE
  /\ fallbackAttempted' = FALSE
  /\ fallbackSucceeded' = FALSE
  /\ returnedSuccess' = TRUE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ requestPending' = FALSE
  /\ UNCHANGED <<cheapCanSucceed, fallbackCanSucceed>>

AttemptCheapFallback ==
  /\ requestPending
  /\ ~cheapAttempted
  /\ ~cheapCanSucceed
  /\ cheapAttempted' = TRUE
  /\ cheapSucceeded' = FALSE
  /\ fallbackRequired' = TRUE
  /\ fallbackAttempted' = FALSE
  /\ fallbackSucceeded' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ requestPending' = TRUE
  /\ UNCHANGED <<cheapCanSucceed, fallbackCanSucceed>>

AttemptFallbackSuccess ==
  /\ requestPending
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = TRUE
  /\ returnedSuccess' = TRUE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ requestPending' = FALSE
  /\ UNCHANGED <<cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired>>

FailExplicitly ==
  /\ requestPending
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ ~fallbackCanSucceed
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = TRUE
  /\ failureReasonPresent' = TRUE
  /\ requestPending' = FALSE
  /\ UNCHANGED <<cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<requestPending, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

Next ==
  AttemptCheapSuccess
  \/ AttemptCheapFallback
  \/ AttemptFallbackSuccess
  \/ FailExplicitly
  \/ Idle

Spec ==
  Init /\ [][Next]_<<
    requestPending,
    cheapCanSucceed,
    fallbackCanSucceed,
    cheapAttempted,
    cheapSucceeded,
    fallbackRequired,
    fallbackAttempted,
    fallbackSucceeded,
    returnedSuccess,
    explicitFailure,
    failureReasonPresent
  >>

PendingRequestEventuallyResolves ==
  [](requestPending => <> Resolved)

Fair ==
  /\ WF_<<requestPending, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(AttemptCheapSuccess)
  /\ WF_<<requestPending, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(AttemptCheapFallback)
  /\ WF_<<requestPending, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(AttemptFallbackSuccess)
  /\ WF_<<requestPending, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(FailExplicitly)

FairImpliesPendingRequestEventuallyResolves ==
  Fair => PendingRequestEventuallyResolves

====
