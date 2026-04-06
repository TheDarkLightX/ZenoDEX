---- MODULE PerpLiquidationBuilderReorgQueue ----
EXTENDS Integers

(*
Bounded TLA+ model for proof-gated liquidation queue drain under bounded external capacity preemption
and one rollback.

Purpose:
- Extend the bounded open-ingress liquidation queue with a limited external capacity-preemption budget
  and one possible rollback of a processed liquidation.
- Model that a pending liquidation queue may receive bounded arrivals, lose bounded per-block capacity
  to competing execution, process a liquidation, suffer at most one rollback, and still eventually
  resolve by drain or breaker under fair control progression.
- Check a narrow, honest control claim under explicit fairness assumptions.

This is intentionally abstract:
- no liquidation pricing,
- no account selection policy,
- no fee markets or builder bidding,
- no multi-reorg behavior,
- only bounded queue pressure, bounded capacity preemption, one rollback, and breaker fallback.
*)

MAX_QUEUE == 4
MAX_PER_BLOCK == 2
ARRIVAL_BUDGET_MAX == 2
BUILDER_PREEMPT_BUDGET_MAX == 1
REORG_BUDGET_MAX == 1

VARIABLES
  queueDepth,
  liquidationsThisBlock,
  arrivalBudget,
  builderPreemptBudget,
  proofOk,
  bindingOk,
  insuranceHealthy,
  breaker,
  blockPhase,
  processedPending,
  reorgBudget

Resolved ==
  ((queueDepth = 0) /\ ~processedPending) \/ breaker

SafeToProcess ==
  queueDepth > 0 /\ proofOk /\ bindingOk /\ insuranceHealthy /\ ~breaker /\ ~processedPending

UnsafePending ==
  queueDepth > 0 /\ (~proofOk \/ ~bindingOk \/ ~insuranceHealthy) /\ ~breaker /\ ~processedPending

TypeOK ==
  /\ queueDepth \in 0..MAX_QUEUE
  /\ liquidationsThisBlock \in 0..MAX_PER_BLOCK
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
  /\ proofOk \in BOOLEAN
  /\ bindingOk \in BOOLEAN
  /\ insuranceHealthy \in BOOLEAN
  /\ breaker \in BOOLEAN
  /\ blockPhase \in {0, 1}
  /\ processedPending \in BOOLEAN
  /\ reorgBudget \in 0..REORG_BUDGET_MAX

GuardConsistent ==
  /\ liquidationsThisBlock <= MAX_PER_BLOCK
  /\ processedPending => liquidationsThisBlock >= 1
  /\ processedPending => ~breaker
  /\ breaker => queueDepth >= 0

Init ==
  /\ queueDepth \in 0..(MAX_QUEUE - ARRIVAL_BUDGET_MAX)
  /\ liquidationsThisBlock \in 0..MAX_PER_BLOCK
  /\ arrivalBudget \in 0..ARRIVAL_BUDGET_MAX
  /\ builderPreemptBudget \in 0..BUILDER_PREEMPT_BUDGET_MAX
  /\ proofOk \in BOOLEAN
  /\ bindingOk \in BOOLEAN
  /\ insuranceHealthy \in BOOLEAN
  /\ breaker = FALSE
  /\ blockPhase = 0
  /\ processedPending = FALSE
  /\ reorgBudget \in 0..REORG_BUDGET_MAX

IngressArrival ==
  /\ queueDepth < MAX_QUEUE
  /\ arrivalBudget > 0
  /\ ~breaker
  /\ queueDepth' = queueDepth + 1
  /\ arrivalBudget' = arrivalBudget - 1
  /\ UNCHANGED <<liquidationsThisBlock, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, processedPending, reorgBudget>>

ProcessLiquidation ==
  /\ SafeToProcess
  /\ liquidationsThisBlock < MAX_PER_BLOCK
  /\ queueDepth' = queueDepth - 1
  /\ liquidationsThisBlock' = liquidationsThisBlock + 1
  /\ processedPending' = TRUE
  /\ UNCHANGED <<arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, reorgBudget>>

FinalizeProcessed ==
  /\ processedPending
  /\ ~breaker
  /\ processedPending' = FALSE
  /\ UNCHANGED <<queueDepth, liquidationsThisBlock, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, reorgBudget>>

SingleReorgRollback ==
  /\ processedPending
  /\ ~breaker
  /\ reorgBudget > 0
  /\ queueDepth < MAX_QUEUE
  /\ queueDepth' = queueDepth + 1
  /\ processedPending' = FALSE
  /\ reorgBudget' = reorgBudget - 1
  /\ UNCHANGED <<liquidationsThisBlock, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>

BuilderPreemptCapacity ==
  /\ queueDepth > 0
  /\ ~breaker
  /\ ~processedPending
  /\ liquidationsThisBlock < MAX_PER_BLOCK
  /\ builderPreemptBudget > 0
  /\ liquidationsThisBlock' = liquidationsThisBlock + 1
  /\ builderPreemptBudget' = builderPreemptBudget - 1
  /\ UNCHANGED <<queueDepth, arrivalBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, processedPending, reorgBudget>>

AdvanceBlock ==
  /\ ~breaker
  /\ ~processedPending
  /\ liquidationsThisBlock = MAX_PER_BLOCK
  /\ liquidationsThisBlock' = 0
  /\ blockPhase' = 1 - blockPhase
  /\ UNCHANGED <<queueDepth, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, processedPending, reorgBudget>>

TripBreaker ==
  /\ UnsafePending
  /\ breaker' = TRUE
  /\ UNCHANGED <<queueDepth, liquidationsThisBlock, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, blockPhase, processedPending, reorgBudget>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, liquidationsThisBlock, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, processedPending, reorgBudget>>

Next ==
  IngressArrival
  \/ ProcessLiquidation
  \/ FinalizeProcessed
  \/ SingleReorgRollback
  \/ BuilderPreemptCapacity
  \/ AdvanceBlock
  \/ TripBreaker
  \/ Idle

Spec ==
  Init /\ [][Next]_<<queueDepth, liquidationsThisBlock, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, processedPending, reorgBudget>>

BuilderReorgEventuallyResolves ==
  [](((((queueDepth > 0) \/ processedPending) /\ ~breaker)) => <> Resolved)

ProcessedPendingEventuallyFinalizesOrRollsBack ==
  []((processedPending /\ ~breaker) => <> (~processedPending))

SafePendingWithoutRemainingAdversaryEventuallyDrains ==
  [](((((queueDepth > 0) \/ processedPending) /\ proofOk /\ bindingOk /\ insuranceHealthy /\ ~breaker) /\ arrivalBudget = 0 /\ builderPreemptBudget = 0 /\ reorgBudget = 0) => <> ((queueDepth = 0) /\ ~processedPending))

UnsafePendingEventuallyBlocks ==
  [](UnsafePending => <> breaker)

Fair ==
  /\ SF_<<queueDepth, liquidationsThisBlock, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, processedPending, reorgBudget>>(ProcessLiquidation)
  /\ WF_<<queueDepth, liquidationsThisBlock, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, processedPending, reorgBudget>>(FinalizeProcessed)
  /\ WF_<<queueDepth, liquidationsThisBlock, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, processedPending, reorgBudget>>(AdvanceBlock)
  /\ WF_<<queueDepth, liquidationsThisBlock, arrivalBudget, builderPreemptBudget, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase, processedPending, reorgBudget>>(TripBreaker)

FairImpliesBuilderReorgEventuallyResolves ==
  Fair => BuilderReorgEventuallyResolves

FairImpliesProcessedPendingEventuallyFinalizesOrRollsBack ==
  Fair => ProcessedPendingEventuallyFinalizesOrRollsBack

FairImpliesSafePendingWithoutRemainingAdversaryEventuallyDrains ==
  Fair => SafePendingWithoutRemainingAdversaryEventuallyDrains

FairImpliesUnsafePendingEventuallyBlocks ==
  Fair => UnsafePendingEventuallyBlocks

====
