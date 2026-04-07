---- MODULE SettlementWitnessFeePriorityReorgQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for settlement witness inclusion under bounded fee-priority pressure and one rollback.

Purpose:
- Extend the bounded settlement witness fee-priority queue with one possible post-inclusion rollback.
- Model that a target witness may be delayed by bounded arrivals ahead, preempted at the head by a
  bounded number of higher-priority competitors, use a bounded number of fee bumps, include, suffer
  at most one rollback, and still eventually resolve under fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no real fee market or bid auction,
- no signature or parsing semantics,
- no multi-reorg behavior,
- only bounded arrivals ahead, bounded higher-priority head preemption, bounded target fee bumps,
  one bounded rollback, and decisive head service.
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
  targetAdmissible,
  arrivalBudget,
  higherPriorityBudget,
  targetFeeLevel,
  targetFeeBumpBudget,
  includedPending,
  finalized,
  rejected,
  reasonPresent,
  reorgBudget

Resolved ==
  finalized \/ rejected

TypeOK ==
  /\ queueDepth \in 0..MAX_QUEUE
  /\ targetPresent \in BOOLEAN
  /\ targetPos \in -1..(MAX_QUEUE - 1)
  /\ targetAdmissible \in BOOLEAN
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ higherPriorityBudget \in 0..HIGHER_PRIORITY_BUDGET_MAX
  /\ targetFeeLevel \in 0..MAX_FEE_LEVEL
  /\ targetFeeBumpBudget \in 0..TARGET_FEE_BUMP_BUDGET_MAX
  /\ includedPending \in BOOLEAN
  /\ finalized \in BOOLEAN
  /\ rejected \in BOOLEAN
  /\ reasonPresent \in BOOLEAN
  /\ reorgBudget \in 0..REORG_BUDGET_MAX

QueueCoherent ==
  /\ targetPresent => queueDepth >= 1
  /\ targetPresent => targetPos >= 0 /\ targetPos < queueDepth
  /\ ~targetPresent => targetPos = -1
  /\ includedPending => ~targetPresent
  /\ includedPending => ~finalized /\ ~rejected /\ ~reasonPresent
  /\ ~(finalized /\ rejected)
  /\ finalized => ~includedPending /\ ~reasonPresent
  /\ rejected => ~includedPending /\ reasonPresent
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
  /\ includedPending = FALSE
  /\ finalized = FALSE
  /\ rejected = FALSE
  /\ reasonPresent = FALSE
  /\ reorgBudget \in 0..REORG_BUDGET_MAX

AdversarialArrivalAhead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~includedPending
  /\ arrivalBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = targetPos + 1
  /\ arrivalBudget' = arrivalBudget - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~includedPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

InvalidateTarget ==
  /\ targetPresent
  /\ targetAdmissible
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~includedPending
  /\ targetAdmissible' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

HigherPriorityPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ targetAdmissible
  /\ ~Resolved
  /\ ~includedPending
  /\ higherPriorityBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ higherPriorityBudget' = higherPriorityBudget - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, arrivalBudget, targetFeeLevel, targetFeeBumpBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

TargetFeeBump ==
  /\ targetPresent
  /\ ~Resolved
  /\ targetFeeBumpBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ targetFeeLevel' = targetFeeLevel + 1
  /\ targetFeeBumpBudget' = targetFeeBumpBudget - 1
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

IncludeTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ targetAdmissible
  /\ ~Resolved
  /\ ~includedPending
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ includedPending' = TRUE
  /\ finalized' = FALSE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, reorgBudget>>

FinalizeIncluded ==
  /\ includedPending
  /\ ~Resolved
  /\ includedPending' = FALSE
  /\ finalized' = TRUE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, reorgBudget>>

SingleReorgRollback ==
  /\ includedPending
  /\ ~Resolved
  /\ reorgBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPresent' = TRUE
  /\ targetPos' \in 0..ReorgHeadroom(queueDepth)
  /\ includedPending' = FALSE
  /\ finalized' = FALSE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ reorgBudget' = reorgBudget - 1
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget>>

RejectTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~targetAdmissible
  /\ ~Resolved
  /\ ~includedPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ includedPending' = FALSE
  /\ finalized' = FALSE
  /\ rejected' = TRUE
  /\ reasonPresent' = TRUE
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, reorgBudget>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

HeadService ==
  HigherPriorityPreemptHead \/ IncludeTarget \/ RejectTarget

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ InvalidateTarget
  \/ HigherPriorityPreemptHead
  \/ TargetFeeBump
  \/ IncludeTarget
  \/ FinalizeIncluded
  \/ SingleReorgRollback
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
    includedPending,
    finalized,
    rejected,
    reasonPresent,
    reorgBudget
  >>

FeePriorityReorgEventuallyResolves ==
  []((((targetPresent \/ includedPending) /\ ~Resolved)) => <> Resolved)

TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  []((targetPresent /\ targetFeeBumpBudget > 0 /\ ~Resolved) => <> (targetFeeBumpBudget = 0 \/ Resolved))

AdmissibleHeadWithoutRemainingPriorityPressureEventuallyIncludes ==
  []((targetPresent /\ targetPos = 0 /\ targetAdmissible /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL) /\ ~Resolved /\ ~includedPending) => <> includedPending)

IncludedPendingEventuallyFinalizesOrRollsBack ==
  []((includedPending /\ ~Resolved) => <> (finalized \/ targetPresent))

InadmissibleHeadEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~targetAdmissible /\ ~Resolved /\ ~includedPending) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>(TargetFeeBump)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>(HeadService)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>(FinalizeIncluded)

FairImpliesFeePriorityReorgEventuallyResolves ==
  Fair => FeePriorityReorgEventuallyResolves

FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  Fair => TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves

FairImpliesAdmissibleHeadWithoutRemainingPriorityPressureEventuallyIncludes ==
  Fair => AdmissibleHeadWithoutRemainingPriorityPressureEventuallyIncludes

FairImpliesIncludedPendingEventuallyFinalizesOrRollsBack ==
  Fair => IncludedPendingEventuallyFinalizesOrRollsBack

FairImpliesInadmissibleHeadEventuallyRejects ==
  Fair => InadmissibleHeadEventuallyRejects

====
