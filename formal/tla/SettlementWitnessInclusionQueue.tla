---- MODULE SettlementWitnessInclusionQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for settlement witness inclusion from a closed queue.

Purpose:
- Capture a simple fairness/inclusion layer above the local settlement witness lifecycle.
- Model a finite closed queue with one distinguished accepted target witness.
- Check that fair queue processing eventually includes an admissible target witness
  or rejects a now-inadmissible target witness with an explicit reason.

This is intentionally abstract:
- no mempool economics,
- no block builder competition,
- no chain reorgs,
- only queue position, admissibility drift, and total dequeue resolution.
*)

MAX_QUEUE == 4

VARIABLES
  queueDepth,
  targetPresent,
  targetPos,
  targetAdmissible,
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
  /\ queueDepth \in 1..MAX_QUEUE
  /\ targetPresent = TRUE
  /\ targetPos \in 0..(queueDepth - 1)
  /\ targetAdmissible = TRUE
  /\ included = FALSE
  /\ rejected = FALSE
  /\ reasonPresent = FALSE

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<targetPresent, targetAdmissible, included, rejected, reasonPresent>>

InvalidateTarget ==
  /\ targetPresent
  /\ targetAdmissible
  /\ targetPos > 0
  /\ ~Resolved
  /\ targetAdmissible' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, included, rejected, reasonPresent>>

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
  /\ UNCHANGED <<targetAdmissible>>

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
  /\ UNCHANGED <<targetAdmissible>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, targetAdmissible, included, rejected, reasonPresent>>

Next ==
  ProcessOtherHead
  \/ InvalidateTarget
  \/ IncludeTarget
  \/ RejectTarget
  \/ Idle

Spec ==
  Init /\ [][Next]_<<queueDepth, targetPresent, targetPos, targetAdmissible, included, rejected, reasonPresent>>

AcceptedTargetEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

AdmissibleHeadEventuallyIncludes ==
  []((targetPresent /\ targetPos = 0 /\ targetAdmissible /\ ~Resolved) => <> included)

InadmissibleHeadEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~targetAdmissible /\ ~Resolved) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, targetAdmissible, included, rejected, reasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, included, rejected, reasonPresent>>(IncludeTarget)
  /\ WF_<<queueDepth, targetPresent, targetPos, targetAdmissible, included, rejected, reasonPresent>>(RejectTarget)

FairImpliesAcceptedTargetEventuallyResolves ==
  Fair => AcceptedTargetEventuallyResolves

FairImpliesAdmissibleHeadEventuallyIncludes ==
  Fair => AdmissibleHeadEventuallyIncludes

FairImpliesInadmissibleHeadEventuallyRejects ==
  Fair => InadmissibleHeadEventuallyRejects

====
