---- MODULE ExactOutAdaptiveFeePriorityReorgQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for exact-out adaptive resolution under bounded fee-priority pressure and one rollback.

Purpose:
- Extend the bounded exact-out adaptive fee-priority queue with one possible post-success rollback.
- Model that a target exact-out request may be delayed by bounded higher-priority pressure, use a
  bounded fee-bump budget, succeed, suffer at most one rollback, and still eventually resolve under
  fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no routing arithmetic,
- no candidate generation,
- no real fee market or bid auction,
- no multi-reorg behavior,
- only bounded arrivals ahead, bounded higher-priority head preemption, bounded target fee bumps,
  one bounded rollback, and adaptive head service.
*)

MAX_QUEUE == 5
ARRIVAL_BUDGET_MAX == 2
HIGHER_PRIORITY_BUDGET_MAX == 1
TARGET_FEE_BUMP_BUDGET_MAX == 2
MAX_FEE_LEVEL == TARGET_FEE_BUMP_BUDGET_MAX
REORG_BUDGET_MAX == 1
REORG_REINSERT_AHEAD_MAX == 1

ReorgHeadroom(q) ==
  IF q < REORG_REINSERT_AHEAD_MAX THEN q ELSE REORG_REINSERT_AHEAD_MAX

VARIABLES
  queueDepth,
  targetPresent,
  targetPos,
  arrivalBudget,
  higherPriorityBudget,
  targetFeeLevel,
  targetFeeBumpBudget,
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
  /\ higherPriorityBudget \in 0..HIGHER_PRIORITY_BUDGET_MAX
  /\ targetFeeLevel \in 0..MAX_FEE_LEVEL
  /\ targetFeeBumpBudget \in 0..TARGET_FEE_BUMP_BUDGET_MAX
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

PriorityCoherent ==
  /\ targetFeeLevel + targetFeeBumpBudget <= TARGET_FEE_BUMP_BUDGET_MAX
  /\ targetFeeLevel = MAX_FEE_LEVEL => targetFeeBumpBudget = 0

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
  /\ higherPriorityBudget \in 0..HIGHER_PRIORITY_BUDGET_MAX
  /\ targetFeeLevel = 0
  /\ targetFeeBumpBudget \in 0..TARGET_FEE_BUMP_BUDGET_MAX
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
  /\ UNCHANGED <<higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget, targetPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~successPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget, targetPresent>>

LoseCheapAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ cheapCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ ~cheapAttempted
  /\ cheapCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>

LoseFallbackAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ fallbackCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>

HigherPriorityPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Resolved
  /\ ~successPending
  /\ higherPriorityBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ higherPriorityBudget' = higherPriorityBudget - 1
  /\ UNCHANGED <<targetPresent, arrivalBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>

TargetFeeBump ==
  /\ targetPresent
  /\ ~Resolved
  /\ targetFeeBumpBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ targetFeeLevel' = targetFeeLevel + 1
  /\ targetFeeBumpBudget' = targetFeeBumpBudget - 1
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>

AttemptCheapSuccess ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~cheapAttempted
  /\ cheapCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
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
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, reorgBudget>>

AttemptCheapFallback ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~cheapAttempted
  /\ ~cheapCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
  /\ cheapAttempted' = TRUE
  /\ cheapSucceeded' = FALSE
  /\ fallbackRequired' = TRUE
  /\ fallbackAttempted' = FALSE
  /\ fallbackSucceeded' = FALSE
  /\ successPending' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, reorgBudget>>

AttemptFallbackSuccess ==
  /\ targetPresent
  /\ targetPos = 0
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = TRUE
  /\ successPending' = TRUE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, reorgBudget>>

FinalizeSuccess ==
  /\ successPending
  /\ ~Resolved
  /\ successPending' = FALSE
  /\ returnedSuccess' = TRUE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, reorgBudget>>

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
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed>>

FailExplicitly ==
  /\ targetPresent
  /\ targetPos = 0
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ ~fallbackCanSucceed
  /\ ~Resolved
  /\ ~successPending
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = FALSE
  /\ successPending' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = TRUE
  /\ failureReasonPresent' = TRUE
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, reorgBudget>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>

HeadService ==
  HigherPriorityPreemptHead
  \/ AttemptCheapSuccess
  \/ AttemptCheapFallback
  \/ AttemptFallbackSuccess
  \/ FailExplicitly

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ LoseCheapAvailability
  \/ LoseFallbackAvailability
  \/ HigherPriorityPreemptHead
  \/ TargetFeeBump
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
    higherPriorityBudget,
    targetFeeLevel,
    targetFeeBumpBudget,
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

FeePriorityReorgEventuallyResolves ==
  []((((targetPresent \/ successPending) /\ ~Resolved)) => <> Resolved)

TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  []((targetPresent /\ targetFeeBumpBudget > 0 /\ ~Resolved) => <> (targetFeeBumpBudget = 0 \/ Resolved))

CheapHeadWithoutRemainingPriorityPressureEventuallyEntersSuccessPending ==
  []((targetPresent /\ targetPos = 0 /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL) /\ cheapCanSucceed /\ ~Resolved /\ ~successPending /\ ~cheapAttempted) => <> successPending)

FallbackHeadWithoutRemainingPriorityPressureEventuallyEntersSuccessPending ==
  []((targetPresent /\ targetPos = 0 /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL) /\ ~cheapCanSucceed /\ fallbackCanSucceed /\ fallbackRequired /\ ~fallbackAttempted /\ ~Resolved /\ ~successPending) => <> successPending)

SuccessPendingEventuallyFinalizesOrRollsBack ==
  []((successPending /\ ~Resolved) => <> (returnedSuccess \/ targetPresent))

NoPathHeadWithoutRemainingPriorityPressureEventuallyFailsExplicitly ==
  []((targetPresent /\ targetPos = 0 /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL) /\ ~cheapCanSucceed /\ ~fallbackCanSucceed /\ fallbackRequired /\ ~fallbackAttempted /\ ~Resolved /\ ~successPending) => <> (explicitFailure /\ failureReasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(TargetFeeBump)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(HeadService)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, successPending, returnedSuccess, explicitFailure, failureReasonPresent, reorgBudget>>(FinalizeSuccess)

FairImpliesFeePriorityReorgEventuallyResolves ==
  Fair => FeePriorityReorgEventuallyResolves

FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  Fair => TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves

FairImpliesCheapHeadWithoutRemainingPriorityPressureEventuallyEntersSuccessPending ==
  Fair => CheapHeadWithoutRemainingPriorityPressureEventuallyEntersSuccessPending

FairImpliesFallbackHeadWithoutRemainingPriorityPressureEventuallyEntersSuccessPending ==
  Fair => FallbackHeadWithoutRemainingPriorityPressureEventuallyEntersSuccessPending

FairImpliesSuccessPendingEventuallyFinalizesOrRollsBack ==
  Fair => SuccessPendingEventuallyFinalizesOrRollsBack

FairImpliesNoPathHeadWithoutRemainingPriorityPressureEventuallyFailsExplicitly ==
  Fair => NoPathHeadWithoutRemainingPriorityPressureEventuallyFailsExplicitly

====
