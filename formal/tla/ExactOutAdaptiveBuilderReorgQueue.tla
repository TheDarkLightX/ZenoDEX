---- MODULE ExactOutAdaptiveBuilderReorgQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for exact-out adaptive resolution under bounded head preemption and one rollback.

Purpose:
- Extend the bounded exact-out adaptive queue with both builder-style head preemption and
  one possible post-success rollback.
- Model that a target exact-out request may be delayed by bounded arrivals ahead, preempted
  at the head a bounded number of times, succeed, suffer at most one rollback, and still
  eventually resolve under fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no routing arithmetic,
- no candidate generation,
- no fee markets or builder bidding,
- no multi-reorg behavior,
- only bounded arrivals ahead, bounded head preemption, one bounded rollback, and adaptive head service.
*)

MAX_QUEUE == 5
ARRIVAL_BUDGET_MAX == 2
BUILDER_PREEMPT_BUDGET_MAX == 1
REORG_BUDGET_MAX == 1
REORG_REINSERT_AHEAD_MAX == 1

ReorgHeadroom(q) ==
  IF q < REORG_REINSERT_AHEAD_MAX THEN q ELSE REORG_REINSERT_AHEAD_MAX

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
  successPending,
  returnedSuccess,
  explicitFailure,
  failureReasonPresent,
  reorgBudget

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
  /\ successPending \in BOOLEAN
  /\ returnedSuccess \in BOOLEAN
  /\ explicitFailure \in BOOLEAN
  /\ failureReasonPresent \in BOOLEAN
  /\ reorgBudget \in 0..REORG_BUDGET_MAX

QueueCoherent ==
  /\ targetPresent => queueDepth >= 1
  /\ targetPresent => targetPos >= 0 /\ targetPos < queueDepth
  /\ ~targetPresent => targetPos = -1

BranchCoherent ==
  /\ cheapSucceeded => cheapAttempted
  /\ fallbackRequired => cheapAttempted /\ ~cheapSucceeded
  /\ fallbackAttempted => fallbackRequired
  /\ fallbackSucceeded => fallbackAttempted
  /\ successPending => ~targetPresent /\ ~returnedSuccess /\ ~explicitFailure /\ ~failureReasonPresent
  /\ returnedSuccess => ~successPending /\ ~failureReasonPresent
  /\ explicitFailure => ~successPending /\ failureReasonPresent
  /\ returnedSuccess => cheapSucceeded \/ fallbackSucceeded
  /\ ~(returnedSuccess /\ explicitFailure)
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
  /\ successPending = FALSE
  /\ returnedSuccess = FALSE
  /\ explicitFailure = FALSE
  /\ failureReasonPresent = FALSE
  /\ reorgBudget \in 0..REORG_BUDGET_MAX

AdversarialArrivalAhead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~successPending
  /\ arrivalBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = targetPos + 1
  /\ arrivalBudget' = arrivalBudget - 1
  /\ UNCHANGED <<builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget, targetPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~successPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget, targetPresent>>

LoseCheapAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ cheapCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ ~cheapAttempted
  /\ cheapCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>

LoseFallbackAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ fallbackCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>

BuilderPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Resolved
  /\ ~successPending
  /\ builderPreemptBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ builderPreemptBudget' = builderPreemptBudget - 1
  /\ UNCHANGED <<targetPresent, arrivalBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>

AttemptCheapSuccess ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~cheapAttempted
  /\ cheapCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ cheapAttempted' = TRUE
  /\ cheapSucceeded' = TRUE
  /\ fallbackRequired' = FALSE
  /\ fallbackAttempted' = FALSE
  /\ fallbackSucceeded' = FALSE
  /\ successPending' = TRUE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, reorgBudget>>

AttemptCheapFallback ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~cheapAttempted
  /\ ~cheapCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ cheapAttempted' = TRUE
  /\ cheapSucceeded' = FALSE
  /\ fallbackRequired' = TRUE
  /\ fallbackAttempted' = FALSE
  /\ fallbackSucceeded' = FALSE
  /\ successPending' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, reorgBudget>>

AttemptFallbackSuccess ==
  /\ targetPresent
  /\ targetPos = 0
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = TRUE
  /\ successPending' = TRUE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, reorgBudget>>

FinalizeSuccess ==
  /\ successPending
  /\ ~Resolved
  /\ successPending' = FALSE
  /\ returnedSuccess' = TRUE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, reorgBudget>>

SingleReorgRollback ==
  /\ successPending
  /\ ~Resolved
  /\ reorgBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPresent' = TRUE
  /\ targetPos' \in 0..ReorgHeadroom(queueDepth)
  /\ cheapAttempted' = FALSE
  /\ cheapSucceeded' = FALSE
  /\ fallbackRequired' = FALSE
  /\ fallbackAttempted' = FALSE
  /\ fallbackSucceeded' = FALSE
  /\ successPending' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ reorgBudget' = reorgBudget - 1
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed>>

FailExplicitly ==
  /\ targetPresent
  /\ targetPos = 0
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ ~fallbackCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = FALSE
  /\ successPending' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = TRUE
  /\ failureReasonPresent' = TRUE
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, reorgBudget>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ LoseCheapAvailability
  \/ LoseFallbackAvailability
  \/ BuilderPreemptHead
  \/ AttemptCheapSuccess
  \/ AttemptCheapFallback
  \/ AttemptFallbackSuccess
  \/ FinalizeSuccess
  \/ SingleReorgRollback
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
    successPending,
    returnedSuccess,
    explicitFailure,
    failureReasonPresent,
    reorgBudget
  >>

BuilderReorgEventuallyResolves ==
  []((((targetPresent \/ successPending) /\ ~Resolved)) => <> Resolved)

CheapHeadWithoutRemainingPreemptEventuallyEntersSuccessPending ==
  []((targetPresent /\ targetPos = 0 /\ builderPreemptBudget = 0 /\ cheapCanSucceed /\ ~Resolved /\ ~cheapAttempted) => <> successPending)

FallbackHeadWithoutRemainingPreemptEventuallyEntersSuccessPending ==
  []((targetPresent /\ targetPos = 0 /\ builderPreemptBudget = 0 /\ fallbackRequired /\ fallbackCanSucceed /\ ~fallbackAttempted /\ ~Resolved) => <> successPending)

SuccessPendingEventuallyFinalizesOrRollsBack ==
  []((successPending /\ ~Resolved) => <> (returnedSuccess \/ targetPresent))

NoPathHeadWithoutRemainingPreemptEventuallyFailsExplicitly ==
  []((targetPresent /\ targetPos = 0 /\ builderPreemptBudget = 0 /\ fallbackRequired /\ ~fallbackCanSucceed /\ ~fallbackAttempted /\ ~Resolved) => <> (explicitFailure /\ failureReasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(AttemptCheapSuccess)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(AttemptCheapFallback)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(AttemptFallbackSuccess)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(FinalizeSuccess)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(FailExplicitly)

FairImpliesBuilderReorgEventuallyResolves ==
  Fair => BuilderReorgEventuallyResolves

FairImpliesCheapHeadWithoutRemainingPreemptEventuallyEntersSuccessPending ==
  Fair => CheapHeadWithoutRemainingPreemptEventuallyEntersSuccessPending

FairImpliesFallbackHeadWithoutRemainingPreemptEventuallyEntersSuccessPending ==
  Fair => FallbackHeadWithoutRemainingPreemptEventuallyEntersSuccessPending

FairImpliesSuccessPendingEventuallyFinalizesOrRollsBack ==
  Fair => SuccessPendingEventuallyFinalizesOrRollsBack

FairImpliesNoPathHeadWithoutRemainingPreemptEventuallyFailsExplicitly ==
  Fair => NoPathHeadWithoutRemainingPreemptEventuallyFailsExplicitly

====
