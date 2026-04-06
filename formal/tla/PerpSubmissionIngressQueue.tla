---- MODULE PerpSubmissionIngressQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for perps submission ingress under finite open queue pressure.

Purpose:
- Compose the existing stream-selection, auth-scope, nonce, and deadline ideas into
  one bounded ingress-resolution model.
- Model a finite number of adversarial arrivals ahead of a target submission.
- Check that fair dequeue still eventually resolves the target by accept or reject.

This is intentionally abstract:
- no signatures or parsing,
- no open mempool economics,
- no builder competition or reorgs,
- only bounded queue position, pre-head validity drift, and decisive head service.
*)

MAX_QUEUE == 5
ARRIVAL_BUDGET_MAX == 2

VARIABLES
  queueDepth,
  targetPresent,
  targetPos,
  arrivalBudget,
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
  /\ rejected => reasonPresent
  /\ accepted => ~reasonPresent
  /\ Resolved => ~targetPresent

Init ==
  /\ queueDepth \in 1..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ targetPresent = TRUE
  /\ targetPos \in 0..(queueDepth - 1)
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
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
  /\ UNCHANGED <<targetPresent, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<targetPresent, arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

LoseStreamSelection ==
  /\ targetPresent
  /\ targetPos > 0
  /\ streamSelectable
  /\ ~Resolved
  /\ streamSelectable' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

LoseAuth ==
  /\ targetPresent
  /\ targetPos > 0
  /\ authValid
  /\ ~Resolved
  /\ authValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, streamSelectable, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

LoseNonce ==
  /\ targetPresent
  /\ targetPos > 0
  /\ nonceValid
  /\ ~Resolved
  /\ nonceValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, streamSelectable, authValid, deadlineValid, accepted, rejected, reasonPresent>>

ExpireDeadline ==
  /\ targetPresent
  /\ targetPos > 0
  /\ deadlineValid
  /\ ~Resolved
  /\ deadlineValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, streamSelectable, authValid, nonceValid, accepted, rejected, reasonPresent>>

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
  /\ UNCHANGED <<arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid>>

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
  /\ UNCHANGED <<arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ LoseStreamSelection
  \/ LoseAuth
  \/ LoseNonce
  \/ ExpireDeadline
  \/ AcceptTarget
  \/ RejectTarget
  \/ Idle

Spec ==
  Init /\ [][Next]_<<queueDepth, targetPresent, targetPos, arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

PendingTargetEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

AdmissibleHeadEventuallyAccepts ==
  []((targetPresent /\ targetPos = 0 /\ Admissible /\ ~Resolved) => <> accepted)

InadmissibleHeadEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~Admissible /\ ~Resolved) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>(AcceptTarget)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>(RejectTarget)

FairImpliesPendingTargetEventuallyResolves ==
  Fair => PendingTargetEventuallyResolves

FairImpliesAdmissibleHeadEventuallyAccepts ==
  Fair => AdmissibleHeadEventuallyAccepts

FairImpliesInadmissibleHeadEventuallyRejects ==
  Fair => InadmissibleHeadEventuallyRejects

====
