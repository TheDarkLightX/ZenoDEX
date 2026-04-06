---- MODULE SettlementWitnessFeePriorityQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for settlement witness inclusion under bounded fee-priority pressure.

Purpose:
- Extend the bounded settlement witness queue with a limited higher-priority head-preemption budget.
- Model that a target witness may be delayed by bounded arrivals ahead, preempted at the head by a
  bounded number of higher-priority competitors, use a bounded number of fee bumps, and still
  eventually resolve under fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no real fee market or bid auction,
- no signature or parsing semantics,
- no reorgs,
- no unbounded public mempool or builder competition,
- only bounded arrivals ahead, bounded higher-priority head preemption, bounded target fee bumps,
  and decisive head service.
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
  targetAdmissible,
  arrivalBudget,
  higherPriorityBudget,
  targetFeeLevel,
  targetFeeBumpBudget,
  included,
  rejected,
  reasonPresent

Resolved ==
  included \/ rejected

TypeOK ==
  /\ queueDepth \in 0..MAX_QUEUE
  /\ targetPresent \in BOOLEAN
  /\ targetPos \in -1..(MAX_QUEUE - 1)
  /\ targetAdmissible \in BOOLEAN
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ higherPriorityBudget \in 0..HIGHER_PRIORITY_BUDGET_MAX
  /\ targetFeeLevel \in 0..MAX_FEE_LEVEL
  /\ targetFeeBumpBudget \in 0..TARGET_FEE_BUMP_BUDGET_MAX
  /\ included \in BOOLEAN
  /\ rejected \in BOOLEAN
  /\ reasonPresent \in BOOLEAN

QueueCoherent ==
  /\ targetPresent => queueDepth >= 1
  /\ targetPresent => targetPos >= 0 /\ targetPos < queueDepth
  /\ ~targetPresent => targetPos = -1
  /\ ~(included /\ rejected)
  /\ included => ~reasonPresent
  /\ rejected => reasonPresent
  /\ Resolved => ~targetPresent

PriorityCoherent ==
  /\ targetFeeLevel + targetFeeBumpBudget <= TARGET_FEE_BUMP_BUDGET_MAX
  /\ targetFeeLevel = MAX_FEE_LEVEL => targetFeeBumpBudget = 0

Init ==
  /\ queueDepth \in 1..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ targetPresent = TRUE
  /\ targetPos \in 0..(queueDepth - 1)
  /\ targetAdmissible = TRUE
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ higherPriorityBudget \in 0..HIGHER_PRIORITY_BUDGET_MAX
  /\ targetFeeLevel = 0
  /\ targetFeeBumpBudget \in 0..TARGET_FEE_BUMP_BUDGET_MAX
  /\ included = FALSE
  /\ rejected = FALSE
  /\ reasonPresent = FALSE

AdversarialArrivalAhead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ arrivalBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = targetPos + 1
  /\ arrivalBudget' = arrivalBudget - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, included, rejected, reasonPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, included, rejected, reasonPresent>>

InvalidateTarget ==
  /\ targetPresent
  /\ targetAdmissible
  /\ targetPos > 0
  /\ ~Resolved
  /\ targetAdmissible' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, included, rejected, reasonPresent>>

HigherPriorityPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ targetAdmissible
  /\ ~Resolved
  /\ higherPriorityBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ higherPriorityBudget' = higherPriorityBudget - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, arrivalBudget, targetFeeLevel, targetFeeBumpBudget, included, rejected, reasonPresent>>

TargetFeeBump ==
  /\ targetPresent
  /\ ~Resolved
  /\ targetFeeBumpBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ targetFeeLevel' = targetFeeLevel + 1
  /\ targetFeeBumpBudget' = targetFeeBumpBudget - 1
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, included, rejected, reasonPresent>>

IncludeTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ targetAdmissible
  /\ ~Resolved
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ included' = TRUE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget>>

RejectTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~targetAdmissible
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ included' = FALSE
  /\ rejected' = TRUE
  /\ reasonPresent' = TRUE
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, included, rejected, reasonPresent>>

HeadService ==
  HigherPriorityPreemptHead \/ IncludeTarget \/ RejectTarget

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ InvalidateTarget
  \/ HigherPriorityPreemptHead
  \/ TargetFeeBump
  \/ IncludeTarget
  \/ RejectTarget
  \/ Idle

Spec ==
  Init /\ [][Next]_<<
    queueDepth,
    targetPresent,
    targetPos,
    targetAdmissible,
    arrivalBudget,
    higherPriorityBudget,
    targetFeeLevel,
    targetFeeBumpBudget,
    included,
    rejected,
    reasonPresent
  >>

FeePriorityEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  []((targetPresent /\ targetFeeBumpBudget > 0 /\ ~Resolved) => <> (targetFeeBumpBudget = 0 \/ Resolved))

AdmissibleHeadWithoutRemainingPriorityPressureEventuallyIncludes ==
  []((targetPresent /\ targetPos = 0 /\ targetAdmissible /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL) /\ ~Resolved) => <> included)

InadmissibleHeadEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~targetAdmissible /\ ~Resolved) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, included, rejected, reasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, included, rejected, reasonPresent>>(TargetFeeBump)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, included, rejected, reasonPresent>>(HeadService)

FairImpliesFeePriorityEventuallyResolves ==
  Fair => FeePriorityEventuallyResolves

FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  Fair => TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves

FairImpliesAdmissibleHeadWithoutRemainingPriorityPressureEventuallyIncludes ==
  Fair => AdmissibleHeadWithoutRemainingPriorityPressureEventuallyIncludes

FairImpliesInadmissibleHeadEventuallyRejects ==
  Fair => InadmissibleHeadEventuallyRejects

====
