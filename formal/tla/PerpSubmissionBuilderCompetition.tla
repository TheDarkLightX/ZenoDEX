---- MODULE PerpSubmissionBuilderCompetition ----
EXTENDS Integers

(*
Bounded TLA+ model for perps submission ingress under bounded builder head preemption.

Purpose:
- Extend the bounded perps ingress queue with a limited builder-style head-preemption budget.
- Model that a target submission may reach the head, be preempted by a bounded number of competing
  inclusions, and still eventually resolve under fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no signatures or parsing,
- no fee markets or bid ordering,
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
  arrivalBudget,
  builderPreemptBudget,
  streamSelectable,
  authValid,
  nonceValid,
  deadlineValid,
  accepted,
  rejected,
  reasonPresent

Resolved ==
  accepted \/ rejected

Admissible ==
  streamSelectable /\ authValid /\ nonceValid /\ deadlineValid

TypeOK ==
  /\ queueDepth \in 0..MAX_QUEUE
  /\ targetPresent \in BOOLEAN
  /\ targetPos \in -1..(MAX_QUEUE - 1)
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
  /\ streamSelectable \in BOOLEAN
  /\ authValid \in BOOLEAN
  /\ nonceValid \in BOOLEAN
  /\ deadlineValid \in BOOLEAN
  /\ accepted \in BOOLEAN
  /\ rejected \in BOOLEAN
  /\ reasonPresent \in BOOLEAN

QueueCoherent ==
  /\ targetPresent => queueDepth >= 1
  /\ targetPresent => targetPos >= 0 /\ targetPos < queueDepth
  /\ ~targetPresent => targetPos = -1
  /\ ~(accepted /\ rejected)
  /\ accepted => ~reasonPresent
  /\ rejected => reasonPresent
  /\ Resolved => ~targetPresent

Init ==
  /\ queueDepth \in 1..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ targetPresent = TRUE
  /\ targetPos \in 0..(queueDepth - 1)
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
  /\ streamSelectable = TRUE
  /\ authValid = TRUE
  /\ nonceValid = TRUE
  /\ deadlineValid = TRUE
  /\ accepted = FALSE
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
  /\ UNCHANGED <<builderPreemptBudget, targetPresent, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, targetPresent, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

LoseStreamSelection ==
  /\ targetPresent
  /\ targetPos > 0
  /\ streamSelectable
  /\ ~Resolved
  /\ streamSelectable' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

LoseAuth ==
  /\ targetPresent
  /\ targetPos > 0
  /\ authValid
  /\ ~Resolved
  /\ authValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

LoseNonce ==
  /\ targetPresent
  /\ targetPos > 0
  /\ nonceValid
  /\ ~Resolved
  /\ nonceValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, deadlineValid, accepted, rejected, reasonPresent>>

ExpireDeadline ==
  /\ targetPresent
  /\ targetPos > 0
  /\ deadlineValid
  /\ ~Resolved
  /\ deadlineValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, accepted, rejected, reasonPresent>>

BuilderPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Resolved
  /\ builderPreemptBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ builderPreemptBudget' = builderPreemptBudget - 1
  /\ UNCHANGED <<targetPresent, arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

AcceptTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ Admissible
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ accepted' = TRUE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid>>

RejectTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Admissible
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ accepted' = FALSE
  /\ rejected' = TRUE
  /\ reasonPresent' = TRUE
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ LoseStreamSelection
  \/ LoseAuth
  \/ LoseNonce
  \/ ExpireDeadline
  \/ BuilderPreemptHead
  \/ AcceptTarget
  \/ RejectTarget
  \/ Idle

Spec ==
  Init /\ [][Next]_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

BuilderCompetitionEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

AdmissibleHeadWithoutRemainingPreemptEventuallyAccepts ==
  []((targetPresent /\ targetPos = 0 /\ Admissible /\ builderPreemptBudget = 0 /\ ~Resolved) => <> accepted)

InadmissibleHeadWithoutRemainingPreemptEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~Admissible /\ builderPreemptBudget = 0 /\ ~Resolved) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>(AcceptTarget)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>(RejectTarget)

FairImpliesBuilderCompetitionEventuallyResolves ==
  Fair => BuilderCompetitionEventuallyResolves

FairImpliesAdmissibleHeadWithoutRemainingPreemptEventuallyAccepts ==
  Fair => AdmissibleHeadWithoutRemainingPreemptEventuallyAccepts

FairImpliesInadmissibleHeadWithoutRemainingPreemptEventuallyRejects ==
  Fair => InadmissibleHeadWithoutRemainingPreemptEventuallyRejects

====
