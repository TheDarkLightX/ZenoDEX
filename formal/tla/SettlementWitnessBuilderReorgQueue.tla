---- MODULE SettlementWitnessBuilderReorgQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for settlement witness inclusion under bounded head preemption and one rollback.

Purpose:
- Extend the bounded settlement witness queue with both builder-style head preemption and one
  possible post-inclusion rollback.
- Model that a target witness may be delayed by bounded arrivals ahead, preempted at the head
  a bounded number of times, include, suffer at most one rollback, and still eventually resolve
  under fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no fee market,
- no builder bidding,
- no signature or parsing semantics,
- no multi-reorg behavior,
- only bounded arrivals ahead, bounded head preemption, one bounded rollback, and decisive head service.
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
  targetAdmissible,
  arrivalBudget,
  builderPreemptBudget,
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
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
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

Init ==
  /\ queueDepth \in 1..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ targetPresent = TRUE
  /\ targetPos \in 0..(queueDepth - 1)
  /\ targetAdmissible = TRUE
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
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
  /\ UNCHANGED <<targetPresent, targetAdmissible, builderPreemptBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~includedPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, arrivalBudget, builderPreemptBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

InvalidateTarget ==
  /\ targetPresent
  /\ targetAdmissible
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~includedPending
  /\ targetAdmissible' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

BuilderPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Resolved
  /\ ~includedPending
  /\ builderPreemptBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ builderPreemptBudget' = builderPreemptBudget - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, arrivalBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

IncludeTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ targetAdmissible
  /\ ~Resolved
  /\ ~includedPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ includedPending' = TRUE
  /\ finalized' = FALSE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, builderPreemptBudget, reorgBudget>>

FinalizeIncluded ==
  /\ includedPending
  /\ ~Resolved
  /\ includedPending' = FALSE
  /\ finalized' = TRUE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, reorgBudget>>

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
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, builderPreemptBudget>>

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
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, builderPreemptBudget, reorgBudget>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ InvalidateTarget
  \/ BuilderPreemptHead
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
    builderPreemptBudget,
    includedPending,
    finalized,
    rejected,
    reasonPresent,
    reorgBudget
  >>

BuilderReorgEventuallyResolves ==
  []((((targetPresent \/ includedPending) /\ ~Resolved)) => <> Resolved)

AdmissibleHeadWithoutRemainingPreemptEventuallyIncludes ==
  []((targetPresent /\ targetPos = 0 /\ targetAdmissible /\ builderPreemptBudget = 0 /\ ~Resolved) => <> includedPending)

IncludedPendingEventuallyFinalizesOrRollsBack ==
  []((includedPending /\ ~Resolved) => <> (finalized \/ targetPresent))

InadmissibleHeadWithoutRemainingPreemptEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~targetAdmissible /\ builderPreemptBudget = 0 /\ ~Resolved) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>(IncludeTarget)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>(FinalizeIncluded)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, includedPending, finalized, rejected, reasonPresent, reorgBudget>>(RejectTarget)

FairImpliesBuilderReorgEventuallyResolves ==
  Fair => BuilderReorgEventuallyResolves

FairImpliesAdmissibleHeadWithoutRemainingPreemptEventuallyIncludes ==
  Fair => AdmissibleHeadWithoutRemainingPreemptEventuallyIncludes

FairImpliesIncludedPendingEventuallyFinalizesOrRollsBack ==
  Fair => IncludedPendingEventuallyFinalizesOrRollsBack

FairImpliesInadmissibleHeadWithoutRemainingPreemptEventuallyRejects ==
  Fair => InadmissibleHeadWithoutRemainingPreemptEventuallyRejects

====
