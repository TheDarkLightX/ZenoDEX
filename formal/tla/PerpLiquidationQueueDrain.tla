---- MODULE PerpLiquidationQueueDrain ----
EXTENDS Integers

(*
Bounded TLA+ model for proof-gated liquidation queue drain.

Purpose:
- Capture temporal obligations behind the liquidation queue guard.
- Model a finite pending queue, per-block liquidation throughput, and breaker fallback.
- Check that a closed pending queue is eventually resolved by drain or breaker.

This is intentionally abstract:
- no liquidation pricing,
- no account selection policy,
- no external liquidity,
- only queue drain / breaker control progression.
*)

MAX_QUEUE == 3
MAX_PER_BLOCK == 2

VARIABLES
  queueDepth,
  liquidationsThisBlock,
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
  /\ proofOk \in BOOLEAN
  /\ bindingOk \in BOOLEAN
  /\ insuranceHealthy \in BOOLEAN
  /\ breaker \in BOOLEAN
  /\ blockPhase \in {0, 1}

GuardConsistent ==
  /\ breaker => queueDepth >= 0
  /\ liquidationsThisBlock <= MAX_PER_BLOCK

Init ==
  /\ queueDepth \in 0..MAX_QUEUE
  /\ liquidationsThisBlock \in 0..MAX_PER_BLOCK
  /\ proofOk \in BOOLEAN
  /\ bindingOk \in BOOLEAN
  /\ insuranceHealthy \in BOOLEAN
  /\ breaker = FALSE
  /\ blockPhase = 0

ProcessLiquidation ==
  /\ SafeToProcess
  /\ liquidationsThisBlock < MAX_PER_BLOCK
  /\ queueDepth' = queueDepth - 1
  /\ liquidationsThisBlock' = liquidationsThisBlock + 1
  /\ UNCHANGED <<proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>

AdvanceBlock ==
  /\ SafeToProcess
  /\ liquidationsThisBlock = MAX_PER_BLOCK
  /\ liquidationsThisBlock' = 0
  /\ blockPhase' = 1 - blockPhase
  /\ UNCHANGED <<queueDepth, proofOk, bindingOk, insuranceHealthy, breaker>>

TripBreaker ==
  /\ UnsafePending
  /\ breaker' = TRUE
  /\ UNCHANGED <<queueDepth, liquidationsThisBlock, proofOk, bindingOk, insuranceHealthy, blockPhase>>

Idle ==
  /\ Resolved
  /\ UNCHANGED <<queueDepth, liquidationsThisBlock, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>

Next ==
  ProcessLiquidation
  \/ AdvanceBlock
  \/ TripBreaker
  \/ Idle

Spec ==
  Init /\ [][Next]_<<queueDepth, liquidationsThisBlock, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>

PendingQueueEventuallyResolves ==
  []((queueDepth > 0 /\ ~breaker) => <> Resolved)

SafePendingEventuallyDrains ==
  [](SafeToProcess => <> (queueDepth = 0))

UnsafePendingEventuallyBlocks ==
  [](UnsafePending => <> breaker)

Fair ==
  /\ SF_<<queueDepth, liquidationsThisBlock, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>(ProcessLiquidation)
  /\ WF_<<queueDepth, liquidationsThisBlock, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>(AdvanceBlock)
  /\ WF_<<queueDepth, liquidationsThisBlock, proofOk, bindingOk, insuranceHealthy, breaker, blockPhase>>(TripBreaker)

FairImpliesPendingQueueEventuallyResolves ==
  Fair => PendingQueueEventuallyResolves

FairImpliesSafePendingEventuallyDrains ==
  Fair => SafePendingEventuallyDrains

FairImpliesUnsafePendingEventuallyBlocks ==
  Fair => UnsafePendingEventuallyBlocks

====
