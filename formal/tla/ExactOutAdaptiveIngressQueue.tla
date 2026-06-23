---- MODULE ExactOutAdaptiveIngressQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for exact-out adaptive request resolution under finite open ingress.

Purpose:
- Extend the local exact-out adaptive control lane with a bounded queue and bounded
  adversarial arrivals ahead of a target request.
- Preserve the adaptive head-service order: cheap path first, repaired fallback second,
  explicit failure if neither path can return a replayable result.
- Check that fair dequeue plus decisive head service eventually resolves the target.

This is intentionally abstract:
- no pool arithmetic,
- no candidate generation,
- no fee markets or builder competition,
- only bounded queue pressure, pre-head availability drift, and adaptive head service.
*)

MAX_QUEUE == 5
ARRIVAL_BUDGET_MAX == 2

VARIABLES
  queueDepth,
  targetPresent,
  targetPos,
  arrivalBudget,
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
  /\ queueDepth \in 0..MAX_QUEUE
  /\ targetPresent \in BOOLEAN
  /\ targetPos \in -1..(MAX_QUEUE - 1)
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
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

QueueCoherent ==
  /\ targetPresent => queueDepth >= 1
  /\ targetPresent => targetPos >= 0 /\ targetPos < queueDepth
  /\ ~targetPresent => targetPos = -1

BranchCoherent ==
  /\ cheapSucceeded => cheapAttempted
  /\ fallbackRequired => cheapAttempted /\ ~cheapSucceeded
  /\ fallbackAttempted => fallbackRequired
  /\ fallbackSucceeded => fallbackAttempted
  /\ returnedSuccess => cheapSucceeded \/ fallbackSucceeded
  /\ ~(returnedSuccess /\ explicitFailure)
  /\ explicitFailure => failureReasonPresent
  /\ Resolved => ~targetPresent

Init ==
  /\ queueDepth \in 1..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ targetPresent = TRUE
  /\ targetPos \in 0..(queueDepth - 1)
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ cheapCanSucceed = TRUE
  /\ fallbackCanSucceed = TRUE
  /\ cheapAttempted = FALSE
  /\ cheapSucceeded = FALSE
  /\ fallbackRequired = FALSE
  /\ fallbackAttempted = FALSE
  /\ fallbackSucceeded = FALSE
  /\ returnedSuccess = FALSE
  /\ explicitFailure = FALSE
  /\ failureReasonPresent = FALSE

AdversarialArrivalAhead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ arrivalBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = targetPos + 1
  /\ arrivalBudget' = arrivalBudget - 1
  /\ UNCHANGED <<cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent, targetPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent, targetPresent>>

LoseCheapAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ cheapCanSucceed
  /\ ~Resolved
  /\ ~cheapAttempted
  /\ cheapCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

LoseFallbackAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ fallbackCanSucceed
  /\ ~Resolved
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, cheapCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

AttemptCheapSuccess ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~cheapAttempted
  /\ cheapCanSucceed
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ cheapAttempted' = TRUE
  /\ cheapSucceeded' = TRUE
  /\ fallbackRequired' = FALSE
  /\ fallbackAttempted' = FALSE
  /\ fallbackSucceeded' = FALSE
  /\ returnedSuccess' = TRUE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<arrivalBudget, cheapCanSucceed, fallbackCanSucceed>>

AttemptCheapFallback ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~cheapAttempted
  /\ ~cheapCanSucceed
  /\ ~Resolved
  /\ cheapAttempted' = TRUE
  /\ cheapSucceeded' = FALSE
  /\ fallbackRequired' = TRUE
  /\ fallbackAttempted' = FALSE
  /\ fallbackSucceeded' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, cheapCanSucceed, fallbackCanSucceed>>

AttemptFallbackSuccess ==
  /\ targetPresent
  /\ targetPos = 0
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = TRUE
  /\ returnedSuccess' = TRUE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired>>

FailExplicitly ==
  /\ targetPresent
  /\ targetPos = 0
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ ~fallbackCanSucceed
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = TRUE
  /\ failureReasonPresent' = TRUE
  /\ UNCHANGED <<arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ LoseCheapAvailability
  \/ LoseFallbackAvailability
  \/ AttemptCheapSuccess
  \/ AttemptCheapFallback
  \/ AttemptFallbackSuccess
  \/ FailExplicitly
  \/ Idle

Spec ==
  Init /\ [][Next]_<<
    queueDepth,
    targetPresent,
    targetPos,
    arrivalBudget,
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

PendingTargetEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

CheapHeadEventuallyReturnsSuccess ==
  []((targetPresent /\ targetPos = 0 /\ cheapCanSucceed /\ ~Resolved /\ ~cheapAttempted) => <> returnedSuccess)

FallbackHeadEventuallyReturnsSuccess ==
  []((targetPresent /\ targetPos = 0 /\ ~cheapCanSucceed /\ fallbackCanSucceed /\ fallbackRequired /\ ~fallbackAttempted /\ ~Resolved) => <> returnedSuccess)

NoPathHeadEventuallyFailsExplicitly ==
  []((targetPresent /\ targetPos = 0 /\ ~cheapCanSucceed /\ ~fallbackCanSucceed /\ fallbackRequired /\ ~fallbackAttempted /\ ~Resolved) => <> (explicitFailure /\ failureReasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(AttemptCheapSuccess)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(AttemptCheapFallback)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(AttemptFallbackSuccess)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(FailExplicitly)

FairImpliesPendingTargetEventuallyResolves ==
  Fair => PendingTargetEventuallyResolves

FairImpliesCheapHeadEventuallyReturnsSuccess ==
  Fair => CheapHeadEventuallyReturnsSuccess

FairImpliesFallbackHeadEventuallyReturnsSuccess ==
  Fair => FallbackHeadEventuallyReturnsSuccess

FairImpliesNoPathHeadEventuallyFailsExplicitly ==
  Fair => NoPathHeadEventuallyFailsExplicitly

====
