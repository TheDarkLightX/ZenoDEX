---- MODULE SettlementWitnessBoundedOpenIngress ----
EXTENDS Integers

(*
Bounded TLA+ model for settlement witness inclusion under finite open ingress.

Purpose:
- Extend the closed-queue inclusion model with a bounded adversarial arrival budget.
- Model a finite number of new arrivals inserted ahead of the target witness.
- Check that fair dequeue still eventually resolves the target once the bounded arrival
  budget is exhausted.

This is intentionally abstract:
- no mempool fee market,
- no builder competition,
- no reorgs,
- only bounded ingress pressure ahead of the target and fair queue service.
*)

MAX_QUEUE == 5
ARRIVAL_BUDGET_MAX == 2

VARIABLES
  queueDepth,
  targetPresent,
  targetPos,
  targetAdmissible,
  arrivalBudget,
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
  /\ included \in BOOLEAN
  /\ rejected \in BOOLEAN
  /\ reasonPresent \in BOOLEAN

QueueCoherent ==
  /\ targetPresent => queueDepth >= 1
  /\ targetPresent => targetPos >= 0 /\ targetPos < queueDepth
  /\ ~targetPresent => targetPos = -1
  /\ ~(included /\ rejected)
  /\ rejected => reasonPresent
  /\ included => ~reasonPresent
  /\ Resolved => ~targetPresent

Init ==
  /\ queueDepth \in 1..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ targetPresent = TRUE
  /\ targetPos \in 0..(queueDepth - 1)
  /\ targetAdmissible = TRUE
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
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
  /\ UNCHANGED <<targetPresent, targetAdmissible, included, rejected, reasonPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, arrivalBudget, included, rejected, reasonPresent>>

InvalidateTarget ==
  /\ targetPresent
  /\ targetAdmissible
  /\ targetPos > 0
  /\ ~Resolved
  /\ targetAdmissible' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, included, rejected, reasonPresent>>

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
  /\ UNCHANGED <<targetAdmissible, arrivalBudget>>

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
  /\ UNCHANGED <<targetAdmissible, arrivalBudget>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, included, rejected, reasonPresent>>

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ InvalidateTarget
  \/ IncludeTarget
  \/ RejectTarget
  \/ Idle

Spec ==
  Init /\ [][Next]_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, included, rejected, reasonPresent>>

BoundedOpenIngressEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

AdmissibleHeadEventuallyIncludes ==
  []((targetPresent /\ targetPos = 0 /\ targetAdmissible /\ ~Resolved) => <> included)

InadmissibleHeadEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~targetAdmissible /\ ~Resolved) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, included, rejected, reasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, included, rejected, reasonPresent>>(IncludeTarget)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, arrivalBudget, included, rejected, reasonPresent>>(RejectTarget)

FairImpliesBoundedOpenIngressEventuallyResolves ==
  Fair => BoundedOpenIngressEventuallyResolves

FairImpliesAdmissibleHeadEventuallyIncludes ==
  Fair => AdmissibleHeadEventuallyIncludes

FairImpliesInadmissibleHeadEventuallyRejects ==
  Fair => InadmissibleHeadEventuallyRejects

====
