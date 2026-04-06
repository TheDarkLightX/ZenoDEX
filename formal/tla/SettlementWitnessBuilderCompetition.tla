---- MODULE SettlementWitnessBuilderCompetition ----
EXTENDS Integers

(*
Bounded TLA+ model for settlement witness inclusion under bounded builder head preemption.

Purpose:
- Extend the bounded settlement queue model with a limited builder-style head-preemption budget.
- Model that a target witness may reach the head, be preempted by a bounded number of competing
  inclusions, and still eventually resolve under fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no fee markets or bid ordering,
- no signature or parsing semantics,
- no reorgs,
- no unbounded builder competition,
- only bounded arrivals ahead, bounded head preemption, and decisive head service.
*)

MAX_QUEUE == 5
ARRIVAL_BUDGET_MAX == 2
BUILDER_PREEMPT_BUDGET_MAX == 2

VARIABLES
  queueDepth,
  targetPresent,
  targetPos,
  targetAdmissible,
  arrivalBudget,
  builderPreemptBudget,
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
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
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

Init ==
  /\ queueDepth \in 1..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ targetPresent = TRUE
  /\ targetPos \in 0..(queueDepth - 1)
  /\ targetAdmissible = TRUE
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
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
  /\ UNCHANGED <<targetPresent, targetAdmissible, builderPreemptBudget, included, rejected, reasonPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, arrivalBudget, builderPreemptBudget, included, rejected, reasonPresent>>

InvalidateTarget ==
  /\ targetPresent
  /\ targetAdmissible
  /\ targetPos > 0
  /\ ~Resolved
  /\ targetAdmissible' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, included, rejected, reasonPresent>>

BuilderPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Resolved
  /\ builderPreemptBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ builderPreemptBudget' = builderPreemptBudget - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, arrivalBudget, included, rejected, reasonPresent>>

IncludeTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ targetAdmissible
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ included' = TRUE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, builderPreemptBudget>>

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
  /\ UNCHANGED <<targetAdmissible, arrivalBudget, builderPreemptBudget>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, included, rejected, reasonPresent>>

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ InvalidateTarget
  \/ BuilderPreemptHead
  \/ IncludeTarget
  \/ RejectTarget
  \/ Idle

Spec ==
  Init /\ [][Next]_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, included, rejected, reasonPresent>>

BuilderCompetitionEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

AdmissibleHeadWithoutRemainingPreemptEventuallyIncludes ==
  []((targetPresent /\ targetPos = 0 /\ targetAdmissible /\ builderPreemptBudget = 0 /\ ~Resolved) => <> included)

InadmissibleHeadWithoutRemainingPreemptEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~targetAdmissible /\ builderPreemptBudget = 0 /\ ~Resolved) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, included, rejected, reasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, included, rejected, reasonPresent>>(IncludeTarget)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, builderPreemptBudget, included, rejected, reasonPresent>>(RejectTarget)

FairImpliesBuilderCompetitionEventuallyResolves ==
  Fair => BuilderCompetitionEventuallyResolves

FairImpliesAdmissibleHeadWithoutRemainingPreemptEventuallyIncludes ==
  Fair => AdmissibleHeadWithoutRemainingPreemptEventuallyIncludes

FairImpliesInadmissibleHeadWithoutRemainingPreemptEventuallyRejects ==
  Fair => InadmissibleHeadWithoutRemainingPreemptEventuallyRejects

====
