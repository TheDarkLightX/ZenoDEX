---- MODULE PerpSubmissionBuilderReorgQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for perps submission ingress under bounded head preemption and one rollback.

Purpose:
- Extend the bounded perps submission queue with both builder-style head preemption and one
  possible post-accept rollback.
- Model that a target submission may be delayed by bounded arrivals ahead, preempted at the head
  a bounded number of times, accept, suffer at most one rollback, and still eventually resolve
  under fair queue service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no signatures or parsing,
- no fee market or builder bidding,
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
  arrivalBudget,
  builderPreemptBudget,
  streamSelectable,
  authValid,
  nonceValid,
  deadlineValid,
  acceptedPending,
  finalized,
  rejected,
  reasonPresent,
  reorgBudget

Resolved ==
  finalized \/ rejected

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
  /\ acceptedPending \in BOOLEAN
  /\ finalized \in BOOLEAN
  /\ rejected \in BOOLEAN
  /\ reasonPresent \in BOOLEAN
  /\ reorgBudget \in 0..REORG_BUDGET_MAX

QueueCoherent ==
  /\ targetPresent => queueDepth >= 1
  /\ targetPresent => targetPos >= 0 /\ targetPos < queueDepth
  /\ ~targetPresent => targetPos = -1
  /\ acceptedPending => ~targetPresent
  /\ acceptedPending => ~finalized /\ ~rejected /\ ~reasonPresent
  /\ ~(finalized /\ rejected)
  /\ finalized => ~acceptedPending /\ ~reasonPresent
  /\ rejected => ~acceptedPending /\ reasonPresent
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
  /\ acceptedPending = FALSE
  /\ finalized = FALSE
  /\ rejected = FALSE
  /\ reasonPresent = FALSE
  /\ reorgBudget \in 0..REORG_BUDGET_MAX

AdversarialArrivalAhead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~acceptedPending
  /\ arrivalBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = targetPos + 1
  /\ arrivalBudget' = arrivalBudget - 1
  /\ UNCHANGED <<targetPresent, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ ~acceptedPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<targetPresent, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>

LoseStreamSelection ==
  /\ targetPresent
  /\ targetPos > 0
  /\ streamSelectable
  /\ ~Resolved
  /\ ~acceptedPending
  /\ streamSelectable' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, authValid, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>

LoseAuth ==
  /\ targetPresent
  /\ targetPos > 0
  /\ authValid
  /\ ~Resolved
  /\ ~acceptedPending
  /\ authValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>

LoseNonce ==
  /\ targetPresent
  /\ targetPos > 0
  /\ nonceValid
  /\ ~Resolved
  /\ ~acceptedPending
  /\ nonceValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>

ExpireDeadline ==
  /\ targetPresent
  /\ targetPos > 0
  /\ deadlineValid
  /\ ~Resolved
  /\ ~acceptedPending
  /\ deadlineValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>

BuilderPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Resolved
  /\ ~acceptedPending
  /\ builderPreemptBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ builderPreemptBudget' = builderPreemptBudget - 1
  /\ UNCHANGED <<targetPresent, arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>

AcceptTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ Admissible
  /\ ~Resolved
  /\ ~acceptedPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ acceptedPending' = TRUE
  /\ finalized' = FALSE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, reorgBudget>>

FinalizeAccepted ==
  /\ acceptedPending
  /\ ~Resolved
  /\ acceptedPending' = FALSE
  /\ finalized' = TRUE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, reorgBudget>>

SingleReorgRollback ==
  /\ acceptedPending
  /\ ~Resolved
  /\ reorgBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPresent' = TRUE
  /\ targetPos' \in 0..ReorgHeadroom(queueDepth)
  /\ acceptedPending' = FALSE
  /\ finalized' = FALSE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ reorgBudget' = reorgBudget - 1
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid>>

RejectTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ ~Admissible
  /\ ~Resolved
  /\ ~acceptedPending
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ acceptedPending' = FALSE
  /\ finalized' = FALSE
  /\ rejected' = TRUE
  /\ reasonPresent' = TRUE
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, reorgBudget>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ LoseStreamSelection
  \/ LoseAuth
  \/ LoseNonce
  \/ ExpireDeadline
  \/ BuilderPreemptHead
  \/ AcceptTarget
  \/ FinalizeAccepted
  \/ SingleReorgRollback
  \/ RejectTarget
  \/ Idle

Spec ==
  Init /\ [][Next]_<<
    queueDepth,
    targetPresent,
    targetPos,
    arrivalBudget,
    builderPreemptBudget,
    streamSelectable,
    authValid,
    nonceValid,
    deadlineValid,
    acceptedPending,
    finalized,
    rejected,
    reasonPresent,
    reorgBudget
  >>

BuilderReorgEventuallyResolves ==
  []((((targetPresent \/ acceptedPending) /\ ~Resolved)) => <> Resolved)

AdmissibleHeadWithoutRemainingPreemptEventuallyAccepts ==
  []((targetPresent /\ targetPos = 0 /\ Admissible /\ builderPreemptBudget = 0 /\ ~Resolved) => <> acceptedPending)

AcceptedPendingEventuallyFinalizesOrRollsBack ==
  []((acceptedPending /\ ~Resolved) => <> (finalized \/ targetPresent))

InadmissibleHeadWithoutRemainingPreemptEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~Admissible /\ builderPreemptBudget = 0 /\ ~Resolved) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>(AcceptTarget)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>(FinalizeAccepted)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, builderPreemptBudget, streamSelectable, authValid, nonceValid, deadlineValid, acceptedPending, finalized, rejected, reasonPresent, reorgBudget>>(RejectTarget)

FairImpliesBuilderReorgEventuallyResolves ==
  Fair => BuilderReorgEventuallyResolves

FairImpliesAdmissibleHeadWithoutRemainingPreemptEventuallyAccepts ==
  Fair => AdmissibleHeadWithoutRemainingPreemptEventuallyAccepts

FairImpliesAcceptedPendingEventuallyFinalizesOrRollsBack ==
  Fair => AcceptedPendingEventuallyFinalizesOrRollsBack

FairImpliesInadmissibleHeadWithoutRemainingPreemptEventuallyRejects ==
  Fair => InadmissibleHeadWithoutRemainingPreemptEventuallyRejects

====
