---- MODULE PerpLiquidationBoundedOpenIngress ----
EXTENDS Integers

(*
Bounded TLA+ model for proof-gated liquidation queue drain under finite open ingress.

Purpose:
- Extend the closed liquidation queue model with a bounded adversarial arrival budget.
- Model a finite number of new liquidation items appearing while the queue is being serviced.
- Check that fair processing still eventually resolves the queue by drain or breaker once
  the bounded arrival budget is exhausted.

This is intentionally abstract:
- no liquidation pricing,
- no account selection policy,
- no fee markets or builder competition,
- no unbounded arrivals,
- only bounded queue pressure, throughput caps, and breaker fallback.
*)

MAX_QUEUE == 4
MAX_PER_BLOCK == 2
ARRIVAL_BUDGET_MAX == 2

VARIABLES
  queueDepth,
  liquidationsThisBlock,
  arrivalBudget,
  proofOk,
  bindingOk,
  insuranceHealthy,
  breaker,
  blockPhase

Resolved ==
  (queueDepth = 0) \/ breaker

SafeToProcess ==
  queueDepth > 0 /\ proofOk /\ bindingOk /\ insuranceHealthy /\ ~breaker

UnsafePending ==
  queueDepth > 0 /\ (~proofOk \/ ~bindingOk \/ ~insuranceHealthy) /\ ~breaker

TypeOK ==
  /\ queueDepth \in 0..MAX_QUEUE
  /\ liquidationsThisBlock \in 0..MAX_PER_BLOCK
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ proofOk \in BOOLEAN
  /\ bindingOk \in BOOLEAN
  /\ insuranceHealthy \in BOOLEAN
  /\ breaker \in BOOLEAN
  /\ blockPhase \in {0, 1}

GuardConsistent ==
  /\ liquidationsThisBlock <= MAX_PER_BLOCK
  /\ breaker => queueDepth >= 0

Init ==
  /\ queueDepth \in 0..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ liquidationsThisBlock \in 0..MAX_PER_BLOCK
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ proofOk \in BOOLEAN
  /\ bindingOk \in BOOLEAN
  /\ insuranceHealthy \in BOOLEAN
  /\ breaker = FALSE
  /\ blockPhase = 0

IngressArrival ==
  /\ queueDepth < MAX_QUEUE
  /\ arrivalBudget > 0
  /\ ~breaker
  /\ queueDepth' = queueDepth + 1
  /\ arrivalBudget' = arrivalBudget - 1
  /\ UNCHANGED <<liquidationsThisBlock, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>

ProcessLiquidation ==
  /\ SafeToProcess
  /\ liquidationsThisBlock < MAX_PER_BLOCK
  /\ queueDepth' = queueDepth - 1
  /\ liquidationsThisBlock' = liquidationsThisBlock + 1
  /\ UNCHANGED <<arrivalBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>

AdvanceBlock ==
  /\ SafeToProcess
  /\ liquidationsThisBlock = MAX_PER_BLOCK
  /\ liquidationsThisBlock' = 0
  /\ blockPhase' = 1 - blockPhase
  /\ UNCHANGED <<queueDepth, arrivalBudget, proofOk, bindingOk, insuranceHealthy, breaker>>

TripBreaker ==
  /\ UnsafePending
  /\ breaker' = TRUE
  /\ UNCHANGED <<queueDepth, liquidationsThisBlock, arrivalBudget, proofOk, bindingOk, insuranceHealthy, blockPhase>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, liquidationsThisBlock, arrivalBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>

Next ==
  IngressArrival
  \/ ProcessLiquidation
  \/ AdvanceBlock
  \/ TripBreaker
  \/ Idle

Spec ==
  Init /\ [][Next]_<<queueDepth, liquidationsThisBlock, arrivalBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>

PendingQueueEventuallyResolves ==
  []((queueDepth > 0 /\ ~breaker) => <> Resolved)

SafePendingWithoutFurtherArrivalsEventuallyDrains ==
  []((SafeToProcess /\ arrivalBudget = 0) => <> (queueDepth = 0))

UnsafePendingEventuallyBlocks ==
  [](UnsafePending => <> breaker)

Fair ==
  /\ SF_<<queueDepth, liquidationsThisBlock, arrivalBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>(ProcessLiquidation)
  /\ WF_<<queueDepth, liquidationsThisBlock, arrivalBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>(AdvanceBlock)
  /\ WF_<<queueDepth, liquidationsThisBlock, arrivalBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>(TripBreaker)

FairImpliesPendingQueueEventuallyResolves ==
  Fair => PendingQueueEventuallyResolves

FairImpliesSafePendingWithoutFurtherArrivalsEventuallyDrains ==
  Fair => SafePendingWithoutFurtherArrivalsEventuallyDrains

FairImpliesUnsafePendingEventuallyBlocks ==
  Fair => UnsafePendingEventuallyBlocks

====
