---- MODULE PerpSubmissionFeePriorityQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for perps submission ingress under bounded fee-priority pressure.

Purpose:
- Extend the bounded perps ingress queue with a limited higher-priority head-preemption budget and
  bounded target fee bumps.
- Model that a target submission may reach the head, be delayed by bounded higher-priority
  competitors, use a bounded fee-bump budget, and still eventually resolve under fair queue
  service.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no signatures or parsing,
- no real fee market or bid auction,
- no reorgs,
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
  arrivalBudget,
  higherPriorityBudget,
  targetFeeLevel,
  targetFeeBumpBudget,
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
  /\ higherPriorityBudget \in 0..HIGHER_PRIORITY_BUDGET_MAX
  /\ targetFeeLevel \in 0..MAX_FEE_LEVEL
  /\ targetFeeBumpBudget \in 0..TARGET_FEE_BUMP_BUDGET_MAX
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

PriorityCoherent ==
  /\ targetFeeLevel + targetFeeBumpBudget <= TARGET_FEE_BUMP_BUDGET_MAX
  /\ targetFeeLevel = MAX_FEE_LEVEL => targetFeeBumpBudget = 0

Init ==
  /\ queueDepth \in 1..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ targetPresent = TRUE
  /\ targetPos \in 0..(queueDepth - 1)
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ higherPriorityBudget \in 0..HIGHER_PRIORITY_BUDGET_MAX
  /\ targetFeeLevel = 0
  /\ targetFeeBumpBudget \in 0..TARGET_FEE_BUMP_BUDGET_MAX
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
  /\ UNCHANGED <<higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, targetPresent, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

ProcessOtherHead ==
  /\ targetPresent
  /\ targetPos > 0
  /\ ~Resolved
  /\ queueDepth' = queueDepth - 1
  /\ targetPos' = targetPos - 1
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, targetPresent, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

LoseStreamSelection ==
  /\ targetPresent
  /\ targetPos > 0
  /\ streamSelectable
  /\ ~Resolved
  /\ streamSelectable' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

LoseAuth ==
  /\ targetPresent
  /\ targetPos > 0
  /\ authValid
  /\ ~Resolved
  /\ authValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

LoseNonce ==
  /\ targetPresent
  /\ targetPos > 0
  /\ nonceValid
  /\ ~Resolved
  /\ nonceValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, deadlineValid, accepted, rejected, reasonPresent>>

ExpireDeadline ==
  /\ targetPresent
  /\ targetPos > 0
  /\ deadlineValid
  /\ ~Resolved
  /\ deadlineValid' = FALSE
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, nonceValid, accepted, rejected, reasonPresent>>

HigherPriorityPreemptHead ==
  /\ targetPresent
  /\ targetPos = 0
  /\ Admissible
  /\ ~Resolved
  /\ higherPriorityBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ targetPos' = 1
  /\ higherPriorityBudget' = higherPriorityBudget - 1
  /\ UNCHANGED <<targetPresent, arrivalBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

TargetFeeBump ==
  /\ targetPresent
  /\ ~Resolved
  /\ targetFeeBumpBudget > 0
  /\ targetFeeLevel < MAX_FEE_LEVEL
  /\ targetFeeLevel' = targetFeeLevel + 1
  /\ targetFeeBumpBudget' = targetFeeBumpBudget - 1
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

AcceptTarget ==
  /\ targetPresent
  /\ targetPos = 0
  /\ Admissible
  /\ ~Resolved
  /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL)
  /\ queueDepth' = queueDepth - 1
  /\ targetPresent' = FALSE
  /\ targetPos' = -1
  /\ accepted' = TRUE
  /\ rejected' = FALSE
  /\ reasonPresent' = FALSE
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, nonceValid, deadlineValid>>

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
  /\ UNCHANGED <<arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, nonceValid, deadlineValid>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

HeadService ==
  HigherPriorityPreemptHead \/ AcceptTarget \/ RejectTarget

Next ==
  AdversarialArrivalAhead
  \/ ProcessOtherHead
  \/ LoseStreamSelection
  \/ LoseAuth
  \/ LoseNonce
  \/ ExpireDeadline
  \/ HigherPriorityPreemptHead
  \/ TargetFeeBump
  \/ AcceptTarget
  \/ RejectTarget
  \/ Idle

Spec ==
  Init /\ [][Next]_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>

FeePriorityEventuallyResolves ==
  []((targetPresent /\ ~Resolved) => <> Resolved)

TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  []((targetPresent /\ targetFeeBumpBudget > 0 /\ ~Resolved) => <> (targetFeeBumpBudget = 0 \/ Resolved))

AdmissibleHeadWithoutRemainingPriorityPressureEventuallyAccepts ==
  []((targetPresent /\ targetPos = 0 /\ Admissible /\ (higherPriorityBudget = 0 \/ targetFeeLevel = MAX_FEE_LEVEL) /\ ~Resolved) => <> accepted)

InadmissibleHeadEventuallyRejects ==
  []((targetPresent /\ targetPos = 0 /\ ~Admissible /\ ~Resolved) => <> (rejected /\ reasonPresent))

Fair ==
  /\ SF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>(ProcessOtherHead)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>(TargetFeeBump)
  /\ WF_<<queueDepth, targetPresent, targetPos, arrivalBudget, higherPriorityBudget, targetFeeLevel, targetFeeBumpBudget, streamSelectable, authValid, nonceValid, deadlineValid, accepted, rejected, reasonPresent>>(HeadService)

FairImpliesFeePriorityEventuallyResolves ==
  Fair => FeePriorityEventuallyResolves

FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves ==
  Fair => TargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves

FairImpliesAdmissibleHeadWithoutRemainingPriorityPressureEventuallyAccepts ==
  Fair => AdmissibleHeadWithoutRemainingPriorityPressureEventuallyAccepts

FairImpliesInadmissibleHeadEventuallyRejects ==
  Fair => InadmissibleHeadEventuallyRejects

====
