---
title: README
type: note
permalink: autonomous-tau-dex-review/formal/tla/readme
---

# TLA+ / TLC models (ZenoDEX)

This folder contains small, bounded TLA+ models for two different jobs:

- **liveness-level** protocol obligations (“eventually settles”, “no deadlocks”),
- **independent shadow semantics** for selected Tau guard specs, used to reduce semantic drift risk.

These models complement the repo’s safety invariants and mechanized math proofs.

## Generic-token authority composition

Files:

- `formal/tla/GenericTokenAuthorityComposition.tla`
- `formal/tla/GenericTokenAuthorityComposition.cfg`

What it models:

- exact per-asset registration and mint-actor binding;
- wallet, pool, perps, pending-stake, and active-stake token locations;
- mint, faucet mint, burn, transfer, and location moves;
- private transaction staging followed by one checked commit or exact rejection;
- a late-failure batch and an adversarial unbalanced candidate;
- bounded nonce exhaustion without wraparound;
- weak-fair resolution of every staged transaction.

The checked safety properties include per-asset supply equality, immutable
registration and authority, exact nonce deltas, other-asset and other-actor
locality, unauthorized and unregistered rejection, reject-is-no-op, and the
inability of an unbalanced staged candidate to commit. The test suite also
removes the commit-time accounting guard and requires TLC to produce a
counterexample, demonstrating that the guard is material to the claim.

The finite quotient uses two registered assets, one unknown asset, two actors,
`MaxSupply = 2`, and `MaxNonce = 2`. Transitions operate on one distinguished
asset while requiring the other asset to remain unchanged; this removes a
symmetric duplicate state space while retaining the cross-asset locality
obligation.

This model does not establish full `u32` arithmetic, parser or signature
correctness, completeness of the runtime token-location projection,
serialization or root binding, concurrent commit behavior, AMM or perps
economics, staking reward correctness, canonical zUSD semantics, arbitrary
batch length, or progress after nonce exhaustion. Lean covers unbounded local
arithmetic obligations, and generated-reference/runtime tests cover selected
implementation refinement claims.

## Perp epoch scheduler

Files:

- `formal/tla/PerpEpochScheduler.tla`
- `formal/tla/PerpEpochScheduler.cfg`

What it models:

- an epoch-based workflow that must **publish a clearing price** and then **settle** it,
- a v1.1-style **breaker** flag that enforces **reduce-only** position updates while active,
- a bounded progression model with explicit `oracleLastUpdateEpoch`,
- a publish-liveness property for advanced unsettled epochs under weak fairness of publish actions,
- a settle-liveness property for advanced unsettled epochs under weak fairness of settle actions,
- and a post-publication property: once a clearing is visible, the modeled scheduler eventually settles it.

### Run with TLC

Install the TLA+ tools (TLC), then from the repo root:

```bash
bash tools/install_tla_tools.sh
python3 tools/run_tla_models.py
```

Notes:

- The repo does not commit the TLC jar, but `tools/install_tla_tools.sh` downloads it
  to `external/tla-tools/tla2tools.jar`.
- The release gate now runs `tools/run_tla_models.py` fail-closed, so TLC is part of
  the semantic-assurance lane.
- Bounds are intentionally tiny (`EPOCH_MAX=3`) to keep exploration fast.
- This is still a bounded model check, not a full theorem for arbitrary epoch bounds or operator environments.

## Oracle recovery lifecycle

Files:

- `formal/tla/OracleRecoveryLifecycle.tla`
- `formal/tla/OracleRecoveryLifecycle.cfg`

What it models:

- a bounded stale-versus-fresh oracle world with explicit sync alignment,
- a fail-closed permanent-block path,
- a requested risky-op gate that only re-enables once the oracle world is healthy again,
- and progress claims under weak fairness of update, repair, and permanent-block actions
  plus strong fairness of re-enable.

The key temporal claims are:

- stale unblocked oracle state eventually becomes fresh or permanently blocked,
- and, once a risky action is requested in a healthy oracle world, risky ops are eventually
  resolved by re-enable or permanent block.

This model is still intentionally abstract. It does not encode basis points, TCR/recovery arithmetic, or chain-level operator fairness.

## Settlement witness lifecycle

Files:

- `formal/tla/SettlementWitnessLifecycle.tla`
- `formal/tla/SettlementWitnessLifecycle.cfg`

What it models:

- a bounded accept-before-expiry witness world,
- explicit time progression toward expiry,
- optional witness invalidation before resolution,
- and total resolution by settlement or rejection with reason.

The key temporal claim is:

- once a witness is accepted before expiry, it is eventually resolved by settlement or
  rejection with an explicit reason.

This model is intentionally abstract. It does not encode balances, price rails, or any throughput/fair-scheduling guarantees beyond the modeled resolution actions.

## Exact-out adaptive liveness

Files:

- `formal/tla/ExactOutAdaptiveLiveness.tla`
- `formal/tla/ExactOutAdaptiveLiveness.cfg`

What it models:

- the cheap-path-first adaptive exact-out control flow,
- repaired fallback only after cheap-path failure,
- and total request resolution by success or explicit failure.

The key temporal claim is:

- a pending adaptive exact-out request is eventually resolved, and the repaired fallback
  never jumps ahead of the cheap path on the modeled control path.

This model is intentionally abstract. It does not encode routing arithmetic, candidate generation, or throughput guarantees.

## Perp liquidation queue drain

Files:

- `formal/tla/PerpLiquidationQueueDrain.tla`
- `formal/tla/PerpLiquidationQueueDrain.cfg`

What it models:

- a finite pending liquidation queue,
- per-block liquidation throughput caps,
- proof/binding/insurance gated processing,
- and breaker fallback when the queue is unsafe.

The key temporal claims are:

- a pending closed queue is eventually resolved by draining or by breaker activation,
- safe proof-gated queues eventually drain,
- unsafe pending queues eventually block.

This model is intentionally abstract. It does not encode liquidation pricing, executor incentives, or contagion across markets.

## Settlement witness inclusion queue

Files:

- `formal/tla/SettlementWitnessInclusionQueue.tla`
- `formal/tla/SettlementWitnessInclusionQueue.cfg`

What it models:

- a finite closed queue with one distinguished accepted settlement witness,
- fair dequeue of non-target heads,
- include-at-head for admissible targets,
- reject-at-head for inadmissible targets.

The key temporal claims are:

- an accepted target witness in the closed queue is eventually resolved,
- admissible head targets eventually include,
- inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode open mempool arrivals, block-builder competition, reorgs, or execution economics.

## Settlement witness bounded open ingress

Files:

- `formal/tla/SettlementWitnessBoundedOpenIngress.tla`
- `formal/tla/SettlementWitnessBoundedOpenIngress.cfg`

What it models:

- a finite queue with one distinguished target witness,
- a bounded number of adversarial arrivals inserted ahead of that target,
- fair dequeue of non-target heads,
- and decisive include/reject behavior once the target reaches the head.

The key temporal claims are:

- under bounded open ingress, the target witness is eventually resolved,
- admissible head targets eventually include,
- inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode unbounded open mempools, fee markets, builder competition, or reorgs.

## ZenoGraph host/local acceptance shadow

Files:

- `formal/tla/ZenoGraphHostLocalAcceptance.tla`
- `formal/tla/ZenoGraphHostLocalAcceptance.cfg`

What it models:

- host-side proposal creation for a candidate ZenoGraph fact,
- local validation into `valid` or `invalid`,
- local accept/reject actions,
- and the execution-visibility boundary for accepted facts.

The key safety claims are:

- accepted facts require valid local validation,
- execution-visible facts are visible only after local acceptance,
- unknown/invalid validation states never become execution-visible,
- proposal and reject paths remain fail-closed.

This model is intentionally small. It does not encode fact quality, extraction correctness, signature/provenance checks, or broad runtime promotion policy beyond the bounded governance shell.

## Perps submission ingress queue

Files:

- `formal/tla/PerpSubmissionIngressQueue.tla`
- `formal/tla/PerpSubmissionIngressQueue.cfg`

What it models:

- a target perps submission in a finite queue,
- bounded arrivals ahead of that target,
- pre-head drift of stream/auth/nonce/deadline validity,
- and decisive accept-or-reject behavior once the target reaches the head.

The key temporal claims are:

- the target submission is eventually resolved,
- admissible head targets eventually accept,
- inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode signatures, parser semantics, unbounded mempools, or builder competition.

## Settlement witness single reorg queue

Files:

- `formal/tla/SettlementWitnessSingleReorgQueue.tla`
- `formal/tla/SettlementWitnessSingleReorgQueue.cfg`

What it models:

- a target settlement witness in a bounded queue,
- bounded arrivals ahead of that target before first inclusion,
- decisive include-at-head for admissible targets,
- at most one post-inclusion rollback,
- and bounded re-resolution after that rollback.

The key temporal claims are:

- with at most one rollback, the target witness is eventually resolved,
- admissible head targets eventually include,
- included targets eventually finalize or roll back for bounded re-resolution,
- inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode fee markets, builder competition, multi-reorg chains, or execution economics.

## Perps submission single reorg queue

Files:

- `formal/tla/PerpSubmissionSingleReorgQueue.tla`
- `formal/tla/PerpSubmissionSingleReorgQueue.cfg`

What it models:

- a target perps submission in a bounded queue,
- bounded arrivals ahead of that target before first acceptance,
- decisive accept-at-head for admissible targets,
- at most one post-accept rollback,
- and bounded re-resolution after that rollback.

The key temporal claims are:

- with at most one rollback, the target submission is eventually resolved,
- admissible head targets eventually accept,
- accepted targets eventually finalize or roll back for bounded re-resolution,
- inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode signatures, parser semantics, fee markets, builder competition, or multi-reorg chains.

## Exact-out adaptive ingress queue

Files:

- `formal/tla/ExactOutAdaptiveIngressQueue.tla`
- `formal/tla/ExactOutAdaptiveIngressQueue.cfg`

What it models:

- a target exact-out request in a bounded queue,
- bounded arrivals ahead of that target,
- pre-head drift of cheap-path and fallback availability,
- and adaptive head service with cheap-first, fallback-second, explicit-failure-last sequencing.

The key temporal claims are:

- the target request is eventually resolved,
- cheap-available heads eventually return success,
- fallback-required heads with fallback availability eventually return success,
- heads with no available path eventually fail explicitly with reason.

This model is intentionally abstract. It does not encode route arithmetic, unbounded public request load, fee markets, or builder competition.

## Settlement witness builder competition

Files:

- `formal/tla/SettlementWitnessBuilderCompetition.tla`
- `formal/tla/SettlementWitnessBuilderCompetition.cfg`

What it models:

- a target settlement witness in a bounded queue,
- bounded arrivals ahead of that target,
- bounded head preemption by a competing builder inclusion,
- pre-head admissibility drift,
- and decisive include-or-reject behavior once preemption budget is exhausted.

The key temporal claims are:

- the target witness is eventually resolved,
- once preemption budget is exhausted, admissible head targets eventually include,
- once preemption budget is exhausted, inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode fee markets, builder bids, reorgs, or unbounded block-construction competition.

## Perps submission builder competition

Files:

- `formal/tla/PerpSubmissionBuilderCompetition.tla`
- `formal/tla/PerpSubmissionBuilderCompetition.cfg`

What it models:

- a target perps submission in a bounded queue,
- bounded arrivals ahead of that target,
- bounded head preemption by a competing builder inclusion,
- pre-head stream/auth/nonce/deadline drift,
- and decisive accept-or-reject behavior once preemption budget is exhausted.

The key temporal claims are:

- the target submission is eventually resolved,
- once preemption budget is exhausted, admissible head targets eventually accept,
- once preemption budget is exhausted, inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode fee markets, signatures, builder bids, reorgs, or unbounded block-construction competition.

## Exact-out adaptive builder competition

Files:

- `formal/tla/ExactOutAdaptiveBuilderCompetition.tla`
- `formal/tla/ExactOutAdaptiveBuilderCompetition.cfg`

What it models:

- a target exact-out request in a bounded queue,
- bounded arrivals ahead of that target,
- bounded head preemption by a competing builder inclusion,
- pre-head drift of cheap-path and fallback availability,
- and adaptive head service once preemption budget is exhausted.

The key temporal claims are:

- the target request is eventually resolved,
- once preemption budget is exhausted, cheap-success heads eventually return success,
- once preemption budget is exhausted, fallback-required heads with fallback availability eventually return success,
- once preemption budget is exhausted, heads with no available path eventually fail explicitly with reason.

This model is intentionally abstract. It does not encode route arithmetic, fee markets, builder bids, reorgs, or unbounded public request load.

## Perp liquidation bounded open ingress

Files:

- `formal/tla/PerpLiquidationBoundedOpenIngress.tla`
- `formal/tla/PerpLiquidationBoundedOpenIngress.cfg`

What it models:

- a bounded liquidation queue with per-block throughput caps,
- a bounded number of new liquidation arrivals while the queue is being serviced,
- proof/binding/insurance gated processing,
- and breaker fallback when the queue is unsafe.

The key temporal claims are:

- a pending queue with bounded arrivals eventually resolves by draining or breaker activation,
- once arrivals are exhausted, safe pending queues eventually drain,
- unsafe pending queues eventually block.

This model is intentionally abstract. It does not encode liquidation pricing, executor incentives, builder competition, or unbounded liquidation flow.

## Perp liquidation builder reorg queue

Files:

- `formal/tla/PerpLiquidationBuilderReorgQueue.tla`
- `formal/tla/PerpLiquidationBuilderReorgQueue.cfg`

What it models:

- a bounded liquidation queue with per-block throughput caps,
- a bounded number of new liquidation arrivals while the queue is being serviced,
- a bounded amount of external per-block capacity preemption,
- one possible rollback of a processed liquidation,
- and breaker fallback when the queue is unsafe.

The key temporal claims are:

- under bounded arrivals, bounded capacity preemption, and at most one rollback, the pending queue eventually resolves by drain or breaker,
- processed liquidations eventually finalize or roll back,
- once adversary budgets are exhausted, safe pending queues eventually drain,
- unsafe pending queues eventually block.

This model is intentionally abstract. It does not encode liquidation pricing, builder bids, or multi-reorg liquidation flow.

## Exact-out adaptive single reorg queue

Files:

- `formal/tla/ExactOutAdaptiveSingleReorgQueue.tla`
- `formal/tla/ExactOutAdaptiveSingleReorgQueue.cfg`

What it models:

- a target exact-out request in a bounded queue,
- bounded arrivals ahead of that target before first success,
- adaptive head service with cheap-first and fallback-second sequencing,
- at most one post-success rollback,
- and bounded re-resolution after that rollback.

The key temporal claims are:

- with at most one rollback, the target request is eventually resolved,
- cheap-success and fallback-success heads eventually enter success-pending,
- pending successes eventually finalize or roll back for bounded re-resolution,
- no-path heads eventually fail explicitly with reason.

This model is intentionally abstract. It does not encode route arithmetic, fee markets, builder competition, or multi-reorg chains.

## Exact-out adaptive fee-priority queue

Files:

- `formal/tla/ExactOutAdaptiveFeePriorityQueue.tla`
- `formal/tla/ExactOutAdaptiveFeePriorityQueue.cfg`

What it models:

- a target exact-out request in a bounded queue,
- bounded arrivals ahead of that target,
- bounded head preemption by higher-priority competitors,
- bounded target fee bumps,
- and adaptive cheap/fallback head service once priority pressure is exhausted.

The key temporal claims are:

- under bounded arrivals, bounded higher-priority head preemption, and bounded target fee bumps, the target request is eventually resolved,
- a target with remaining fee-bump budget eventually consumes that budget or resolves,
- cheap-success and fallback-success heads with no remaining priority pressure eventually return success,
- no-path heads with no remaining priority pressure eventually fail explicitly with reason.

This model is intentionally abstract. It does not encode route arithmetic, a live fee market, builder bidding, or unbounded public request load.

## Exact-out adaptive fee-priority reorg queue

Files:

- `formal/tla/ExactOutAdaptiveFeePriorityReorgQueue.tla`
- `formal/tla/ExactOutAdaptiveFeePriorityReorgQueue.cfg`

What it models:

- a target exact-out request in a bounded queue,
- bounded arrivals ahead of that target,
- bounded head preemption by higher-priority competitors,
- bounded target fee bumps,
- adaptive cheap/fallback head service once priority pressure is exhausted,
- at most one post-success rollback,
- and bounded re-resolution after that rollback.

The key temporal claims are:

- under bounded arrivals, bounded higher-priority head preemption, bounded target fee bumps, and at most one rollback, the target request is eventually resolved,
- a target with remaining fee-bump budget eventually consumes that budget or resolves,
- cheap-success and fallback-success heads with no remaining priority pressure eventually enter success-pending,
- pending successes eventually finalize or roll back for bounded re-resolution,
- no-path heads with no remaining priority pressure eventually fail explicitly with reason.

This model is intentionally abstract. It does not encode route arithmetic, a live fee market, builder bidding, or multi-reorg public request flow.

## Exact-out adaptive builder reorg queue

Files:

- `formal/tla/ExactOutAdaptiveBuilderReorgQueue.tla`
- `formal/tla/ExactOutAdaptiveBuilderReorgQueue.cfg`

What it models:

- a target exact-out request in a bounded queue,
- bounded arrivals ahead of that target,
- bounded builder-style head preemption,
- adaptive head service with cheap-first and fallback-second sequencing,
- at most one post-success rollback,
- and bounded re-resolution after that rollback.

The key temporal claims are:

- under bounded arrivals, bounded head preemption, and at most one rollback, the target request is eventually resolved,
- once preemption budget is exhausted, cheap-success and fallback-success heads eventually enter success-pending,
- pending successes eventually finalize or roll back for bounded re-resolution,
- once preemption budget is exhausted, no-path heads eventually fail explicitly with reason.

This model is intentionally abstract. It does not encode route arithmetic, fee markets, builder bids, or multi-reorg chains.

## Settlement witness builder reorg queue

Files:

- `formal/tla/SettlementWitnessBuilderReorgQueue.tla`
- `formal/tla/SettlementWitnessBuilderReorgQueue.cfg`

What it models:

- a target settlement witness in a bounded queue,
- bounded arrivals ahead of that target,
- bounded builder-style head preemption,
- decisive include-or-reject behavior at the head,
- at most one post-inclusion rollback,
- and bounded re-resolution after that rollback.

The key temporal claims are:

- under bounded arrivals, bounded head preemption, and at most one rollback, the target witness is eventually resolved,
- once preemption budget is exhausted, admissible head targets eventually include,
- included-pending targets eventually finalize or roll back for bounded re-resolution,
- once preemption budget is exhausted, inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode fee markets, builder bids, signature semantics, or multi-reorg chains.

## Settlement witness fee-priority queue

Files:

- `formal/tla/SettlementWitnessFeePriorityQueue.tla`
- `formal/tla/SettlementWitnessFeePriorityQueue.cfg`

What it models:

- a target settlement witness in a bounded queue,
- bounded arrivals ahead of that target,
- bounded head preemption by higher-priority competitors,
- bounded target fee bumps,
- and decisive include-or-reject behavior once priority pressure is exhausted.

The key temporal claims are:

- under bounded arrivals, bounded higher-priority head preemption, and bounded target fee bumps, the target witness is eventually resolved,
- a target with remaining fee-bump budget eventually consumes that budget or resolves,
- admissible head targets with no remaining priority pressure eventually include,
- inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode a live fee market, builder bidding, signature semantics, or unbounded mempool starvation.

## Settlement witness fee-priority reorg queue

Files:

- `formal/tla/SettlementWitnessFeePriorityReorgQueue.tla`
- `formal/tla/SettlementWitnessFeePriorityReorgQueue.cfg`

What it models:

- a target settlement witness in a bounded queue,
- bounded arrivals ahead of that target,
- bounded head preemption by higher-priority competitors,
- bounded target fee bumps,
- at most one post-inclusion rollback,
- and bounded re-resolution after that rollback.

The key temporal claims are:

- under bounded arrivals, bounded higher-priority head preemption, bounded target fee bumps, and at most one rollback, the target witness is eventually resolved,
- a target with remaining fee-bump budget eventually consumes that budget or resolves,
- admissible head targets with no remaining priority pressure eventually include,
- included-pending targets eventually finalize or roll back for bounded re-resolution,
- inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode a live fee market, builder bidding, signature semantics, or multi-reorg chains.

## Perps submission fee-priority queue

Files:

- `formal/tla/PerpSubmissionFeePriorityQueue.tla`
- `formal/tla/PerpSubmissionFeePriorityQueue.cfg`

What it models:

- a target perps submission in a bounded queue,
- bounded arrivals ahead of that target,
- bounded head preemption by higher-priority competitors,
- bounded target fee bumps,
- and decisive accept-or-reject behavior once priority pressure is exhausted.

The key temporal claims are:

- under bounded arrivals, bounded higher-priority head preemption, and bounded target fee bumps, the target submission is eventually resolved,
- a target with remaining fee-bump budget eventually consumes that budget or resolves,
- admissible head targets with no remaining priority pressure eventually accept,
- inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode a live fee market, builder bidding, auth semantics, or unbounded mempool starvation.

## Perps submission builder reorg queue

Files:

- `formal/tla/PerpSubmissionBuilderReorgQueue.tla`
- `formal/tla/PerpSubmissionBuilderReorgQueue.cfg`

What it models:

- a target perps submission in a bounded queue,
- bounded arrivals ahead of that target,
- bounded builder-style head preemption,
- decisive accept-or-reject behavior at the head,
- at most one post-accept rollback,
- and bounded re-resolution after that rollback.

The key temporal claims are:

- under bounded arrivals, bounded head preemption, and at most one rollback, the target submission is eventually resolved,
- once preemption budget is exhausted, admissible head targets eventually accept,
- accepted-pending targets eventually finalize or roll back for bounded re-resolution,
- once preemption budget is exhausted, inadmissible head targets eventually reject with reason.

This model is intentionally abstract. It does not encode fee markets, builder bids, signature semantics, or multi-reorg chains.

## Tau shadow semantics

Files:

- `formal/tla/AutoTraderNonceGuardShadow.tla`
- `formal/tla/AutoTraderNonceGuardShadow.cfg`
- `formal/tla/AutoTraderTxEnvelopeShadow.tla`
- `formal/tla/AutoTraderTxEnvelopeShadow.cfg`
- `formal/tla/OracleFreshnessBoundedShadow.tla`
- `formal/tla/OracleFreshnessBoundedShadow.cfg`
- `formal/tla/OrderIntentCancelExpiryShadow.tla`
- `formal/tla/OrderIntentCancelExpiryShadow.cfg`
- `formal/tla/PerpSubmissionAuthScopeShadow.tla`
- `formal/tla/PerpSubmissionAuthScopeShadow.cfg`
- `formal/tla/PerpIngressSchemaShadow.tla`
- `formal/tla/PerpIngressSchemaShadow.cfg`

What they model:

- the intended meaning of selected Tau guards,
- the modeled perps submission-auth admission semantics,
- a bounded oracle freshness predicate used by modeled guard lanes,
- the cancel/expiry order lifecycle admission semantics used by the modeled
  order-intent lane,
- independently of Tau syntax and evaluation semantics,
- with small invariant sets that are pinned by `tools/check_tau_shadow_assurance.py`.

Run the fail-closed scaffolding check from the repo root:

```bash
python3 tools/check_tau_shadow_assurance.py
```

The release gate treats unresolved semantic deltas on release-blocking properties as a blocker.

## Zeno SDK wallet-sync checkpoint shadow

Files:

- `formal/tla/ZenoSdkWalletSyncCheckpoint.tla`
- `formal/tla/ZenoSdkWalletSyncCheckpoint.cfg`

What it models:

- browser/mobile wallet sync over proof-carrying checkpoint bundles,
- host-computed bundle validation as a Boolean predicate,
- host-computed current-state hash validation as a Boolean predicate,
- accepted initial sync, accepted height advance, accepted same-height refresh,
- and fail-closed rejection for invalid current state, invalid bundle, chain
  mismatch, rollback, and same-height app/checkpoint drift.

The key safety claims are:

- accepted updates require a validated bundle,
- accepted updates from an existing state require a valid current state hash,
- accepted updates never decrease checkpoint height,
- accepted updates cannot change chain id after initial sync,
- same-height accepted updates cannot change app or checkpoint commitments,
- rejected updates do not mutate the wallet-sync state.

This model is intentionally abstract. It does not encode JSON parsing, BLS
signature arithmetic, full ledger replay, wallet signing, or transaction
execution authority.
