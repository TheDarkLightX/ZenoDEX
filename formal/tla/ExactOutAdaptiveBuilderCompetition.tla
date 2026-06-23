---- MODULE ExactOutAdaptiveBuilderCompetition ----
EXTENDS Integers

(*
Bounded TLA+ model for exact-out adaptive resolution under bounded builder head preemption.

Purpose:
- Extend the bounded exact-out adaptive ingress queue with a limited builder-style
  head-preemption budget.
- Model that a target exact-out request may reach the head, be preempted by a bounded
  number of competing inclusions, and still eventually resolve under fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no routing arithmetic,
- no candidate generation,
- no fee markets or builder bidding,
- no reorgs,
- only bounded arrivals ahead, bounded head preemption, and adaptive head service.
*)

MAX_QUEUE == 5
ARRIVAL_BUDGET_MAX == 2
BUILDER_PREEMPT_BUDGET_MAX == 2

VARIABLES
  queueDepth,
  targetPresent,
  targetPos,
  arrivalBudget,
  builderPreemptBudget,
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
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
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
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
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
  /\ UNCHANGED <<builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent, targetPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent, targetPresent>>

LoseCheapAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ cheapCanSucceed
  /\ ~Resolved
  /\ ~cheapAttempted
  /\ cheapCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

LoseFallbackAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ fallbackCanSucceed
  /\ ~Resolved
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

BuilderPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Resolved
  /\ builderPreemptBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ builderPreemptBudget' = builderPreemptBudget - 1
  /\ UNCHANGED <<targetPresent, arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

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
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed>>

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
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed>>

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
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired>>

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
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ LoseCheapAvailability
  \/ LoseFallbackAvailability
  \/ BuilderPreemptHead
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
    builderPreemptBudget,
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

BuilderCompetitionEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

CheapHeadWithoutRemainingPreemptEventuallyReturnsSuccess ==
  []((targetPresent /\ targetPos = 0 /\ builderPreemptBudget = 0 /\ cheapCanSucceed /\ ~Resolved /\ ~cheapAttempted) => <> returnedSuccess)

FallbackHeadWithoutRemainingPreemptEventuallyReturnsSuccess ==
  []((targetPresent /\ targetPos = 0 /\ builderPreemptBudget = 0 /\ ~cheapCanSucceed /\ fallbackCanSucceed /\ fallbackRequired /\ ~fallbackAttempted /\ ~Resolved) => <> returnedSuccess)

NoPathHeadWithoutRemainingPreemptEventuallyFailsExplicitly ==
  []((targetPresent /\ targetPos = 0 /\ builderPreemptBudget = 0 /\ ~cheapCanSucceed /\ ~fallbackCanSucceed /\ fallbackRequired /\ ~fallbackAttempted /\ ~Resolved) => <> (explicitFailure /\ failureReasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(AttemptCheapSuccess)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(AttemptCheapFallback)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(AttemptFallbackSuccess)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(FailExplicitly)

FairImpliesBuilderCompetitionEventuallyResolves ==
  Fair => BuilderCompetitionEventuallyResolves

FairImpliesCheapHeadWithoutRemainingPreemptEventuallyReturnsSuccess ==
  Fair => CheapHeadWithoutRemainingPreemptEventuallyReturnsSuccess

FairImpliesFallbackHeadWithoutRemainingPreemptEventuallyReturnsSuccess ==
  Fair => FallbackHeadWithoutRemainingPreemptEventuallyReturnsSuccess

FairImpliesNoPathHeadWithoutRemainingPreemptEventuallyFailsExplicitly ==
  Fair => NoPathHeadWithoutRemainingPreemptEventuallyFailsExplicitly

====
