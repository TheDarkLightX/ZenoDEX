---- MODULE ExactOutAdaptiveFeePriorityQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for exact-out adaptive resolution under bounded fee-priority pressure.

Purpose:
- Extend the bounded exact-out adaptive ingress queue with a limited higher-priority
  head-preemption budget and bounded target fee bumps.
- Model that a target exact-out request may reach the head, be delayed by bounded
  higher-priority pressure, use a bounded fee-bump budget, and still eventually resolve
  under fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no routing arithmetic,
- no candidate generation,
- no real fee market or bid auction,
- no reorgs,
- only bounded arrivals ahead, bounded higher-priority head preemption, bounded target fee bumps,
  and adaptive head service.
*)

MAX_QUEUE == 5
ARRIVAL_BUDGET_MAX == 2
HIGHER_PRIORITY_BUDGET_MAX == 2
TARGET_FEE_BUMP_BUDGET_MAX == 2
MAX_FEE_LEVEL == TARGET_FEE_BUMP_BUDGET_MAX

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
  /\ returnedSuccess \in BOOLEAN
  /\ explicitFailure \in BOOLEAN
  /\ failureReasonPresent \in BOOLEAN

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
  /\ returnedSuccess => cheapSucceeded \/ fallbackSucceeded
  /\ ~(returnedSuccess /\ explicitFailure)
  /\ explicitFailure => failureReasonPresent
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
  /\ UNCHANGED <<higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent, targetPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent, targetPresent>>

LoseCheapAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ cheapCanSucceed
  /\ ~Resolved
  /\ ~cheapAttempted
  /\ cheapCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

LoseFallbackAvailability ==
  /\ targetPresent
  /\ targetPos > 0
  /\ fallbackCanSucceed
  /\ ~Resolved
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

HigherPriorityPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Resolved
  /\ higherPriorityBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ higherPriorityBudget' = higherPriorityBudget - 1
  /\ UNCHANGED <<targetPresent, arrivalBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

TargetFeeBump ==
  /\ targetPresent
  /\ ~Resolved
  /\ targetFeeBumpBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ targetFeeLevel' = targetFeeLevel + 1
  /\ targetFeeBumpBudget' = targetFeeBumpBudget - 1
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

AttemptCheapSuccess ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~cheapAttempted
  /\ cheapCanSucceed
  /\ ~Resolved
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
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
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed>>

AttemptCheapFallback ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~cheapAttempted
  /\ ~cheapCanSucceed
  /\ ~Resolved
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
  /\ cheapAttempted' = TRUE
  /\ cheapSucceeded' = FALSE
  /\ fallbackRequired' = TRUE
  /\ fallbackAttempted' = FALSE
  /\ fallbackSucceeded' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed>>

AttemptFallbackSuccess ==
  /\ targetPresent
  /\ targetPos = 0
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ fallbackCanSucceed
  /\ ~Resolved
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = TRUE
  /\ returnedSuccess' = TRUE
  /\ explicitFailure' = FALSE
  /\ failureReasonPresent' = FALSE
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired>>

FailExplicitly ==
  /\ targetPresent
  /\ targetPos = 0
  /\ fallbackRequired
  /\ ~fallbackAttempted
  /\ ~fallbackCanSucceed
  /\ ~Resolved
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ fallbackAttempted' = TRUE
  /\ fallbackSucceeded' = FALSE
  /\ returnedSuccess' = FALSE
  /\ explicitFailure' = TRUE
  /\ failureReasonPresent' = TRUE
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>

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
    returnedSuccess,
    explicitFailure,
    failureReasonPresent
  >>

FeePriorityEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  []((targetPresent /\ targetFeeBumpBudget > 0 /\ ~Resolved) => <> (targetFeeBumpBudget = 0 \/ Resolved))

CheapHeadWithoutRemainingPriorityPressureEventuallyReturnsSuccess ==
  []((targetPresent /\ targetPos = 0 /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL) /\ cheapCanSucceed /\ ~Resolved /\ ~cheapAttempted) => <> returnedSuccess)

FallbackHeadWithoutRemainingPriorityPressureEventuallyReturnsSuccess ==
  []((targetPresent /\ targetPos = 0 /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL) /\ ~cheapCanSucceed /\ fallbackCanSucceed /\ fallbackRequired /\ ~fallbackAttempted /\ ~Resolved) => <> returnedSuccess)

NoPathHeadWithoutRemainingPriorityPressureEventuallyFailsExplicitly ==
  []((targetPresent /\ targetPos = 0 /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL) /\ ~cheapCanSucceed /\ ~fallbackCanSucceed /\ fallbackRequired /\ ~fallbackAttempted /\ ~Resolved) => <> (explicitFailure /\ failureReasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(TargetFeeBump)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, cheapCanSucceed, fallbackCanSucceed, cheapAttempted, cheapSucceeded, fallbackRequired, fallbackAttempted, fallbackSucceeded, returnedSuccess, explicitFailure, failureReasonPresent>>(HeadService)

FairImpliesFeePriorityEventuallyResolves ==
  Fair => FeePriorityEventuallyResolves

FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  Fair => TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves

FairImpliesCheapHeadWithoutRemainingPriorityPressureEventuallyReturnsSuccess ==
  Fair => CheapHeadWithoutRemainingPriorityPressureEventuallyReturnsSuccess

FairImpliesFallbackHeadWithoutRemainingPriorityPressureEventuallyReturnsSuccess ==
  Fair => FallbackHeadWithoutRemainingPriorityPressureEventuallyReturnsSuccess

FairImpliesNoPathHeadWithoutRemainingPriorityPressureEventuallyFailsExplicitly ==
  Fair => NoPathHeadWithoutRemainingPriorityPressureEventuallyFailsExplicitly

====
