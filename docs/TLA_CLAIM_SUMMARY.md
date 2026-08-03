# TLA Claim Summary

<!-- Generated from docs/claims_registry.yaml and formal/tla/*.cfg. -->

- Supported TLA claims: `38`
- Discovered TLC models: `38`
- Batch checker: `python3 tools/run_tla_models.py --json`
- Inventory guard: `pytest -q tests/formal/test_tla_claim_inventory.py tests/test_claims_registry.py`

## Safety

### `AutoTraderNonceGuardShadow`

- Claim: `tla:autotrader_nonce_guard_shadow:sequential_nonce_only`
- Module: `formal/tla/AutoTraderNonceGuardShadow.tla`
- Config: `formal/tla/AutoTraderNonceGuardShadow.cfg`
- Invariants: `TypeOK`, `AcceptedOnlySequential`, `RejectedDoesNotAdvance`, `NonceNeverDecreases`
- Properties: _none_
- Statement: In the bounded TLA+ autotrader nonce-guard shadow model (`NONCES = {0,1,2,3,4}`), accepted transitions require the next sequential nonce, rejected transitions do not advance the nonce, and the modeled nonce never decreases.

### `AutoTraderTxEnvelopeShadow`

- Claim: `tla:autotrader_tx_envelope_shadow:requested_envelope_only`
- Module: `formal/tla/AutoTraderTxEnvelopeShadow.tla`
- Config: `formal/tla/AutoTraderTxEnvelopeShadow.cfg`
- Invariants: `TypeOK`, `IdleAlwaysAccepted`, `AcceptedOnlyWhenRequestedEnvelopeValid`, `RejectedRequestedTxHasSpecificReason`
- Properties: _none_
- Statement: In the bounded TLA+ autotrader transaction-envelope shadow model, idle states remain accepted, accepted requested transactions require a valid requested envelope, and rejected requested transactions carry a specific rejection reason.

### `FCISM6J09MigrationCrash`

- Claim: `tla:fcis_m6_j09_migration_crash:phase_crash_retry_safety`
- Module: `formal/tla/FCISM6J09MigrationCrash.tla`
- Config: `formal/tla/FCISM6J09MigrationCrash.cfg`
- Invariants: `TypeOK`, `PhaseShape`, `OneWriter`, `CompleteHistory`, `CompletePublicationAtom`, `NoMixedEvidence`, `CrashObservationClosed`, `FreshAuthorizationLatch`, `DeliveryAckProvenance`, `VarsBounded`
- Properties: _none_
- Statement: In the bounded TLA+ FCIS M6 migration/crash model, the seven migration phases advance only by the declared successor relation, one configured writer is active at a time, complete history/residual/nullifier/outbox cardinalities remain aligned, PRE and POST are the only crash observations, restart clears active authorization, evidence versions do not mix, and acknowledgments cannot precede delivery.

### `OracleFreshnessBoundedShadow`

- Claim: `tla:oracle_freshness_bounded_shadow:future_and_stale_quotes_reject`
- Module: `formal/tla/OracleFreshnessBoundedShadow.tla`
- Config: `formal/tla/OracleFreshnessBoundedShadow.cfg`
- Invariants: `TypeOK`, `AcceptedRequiresQuoteNotFuture`, `AcceptedRequiresBoundedAge`, `FutureQuoteRejected`, `StaleQuoteRejected`
- Properties: _none_
- Statement: In the bounded TLA+ oracle-freshness shadow model, accepted quotes are never from the future and always satisfy the bounded-age constraint; future or stale quotes are rejected by the modeled freshness guard.

### `OrderIntentCancelExpiryShadow`

- Claim: `tla:order_intent_cancel_expiry_shadow:cancelled_or_expired_never_executes`
- Module: `formal/tla/OrderIntentCancelExpiryShadow.tla`
- Config: `formal/tla/OrderIntentCancelExpiryShadow.cfg`
- Invariants: `TypeOK`, `CancelledNeverEmitsIntent`, `CancelledExecutionRejectedWithoutIntent`, `ExpiredExecutionRejectedWithoutIntent`, `EmittedIntentRequiresLiveOrderWithinWindow`
- Properties: _none_
- Statement: In the bounded TLA+ order-intent cancel/expiry shadow model (`MAX_EPOCH = 4`), cancelled orders never emit intents, cancelled or expired executions reject without intent, and emitted intents require a live order within the modeled validity window.

### `PerpIngressSchemaShadow`

- Claim: `tla:perp_ingress_schema_shadow:derived_schema_consistency`
- Module: `formal/tla/PerpIngressSchemaShadow.tla`
- Config: `formal/tla/PerpIngressSchemaShadow.cfg`
- Invariants: `TypeOK`, `ActionSelectionMatchesDerived`, `AuthBundleMatchesDerived`, `IngressPreconditionsMatchDerived`, `AcceptedRequiresSingleModeAndPreconditions`
- Properties: _none_
- Statement: In the bounded TLA+ perps ingress-schema shadow model, the derived action selection, auth bundle, and ingress preconditions all match the modeled outer schema, and accepted ingress requires a single mode together with those derived preconditions.

### `PerpSubmissionAuthScopeShadow`

- Claim: `tla:perp_submission_auth_scope_shadow:mode_and_nonce_semantics`
- Module: `formal/tla/PerpSubmissionAuthScopeShadow.tla`
- Config: `formal/tla/PerpSubmissionAuthScopeShadow.cfg`
- Invariants: `TypeOK`, `AcceptedRequiresExactlyOneMode`, `AcceptedSignedModeRequiresAllSignedChecks`, `SenderBoundModeNeverConsumesNonce`, `NonceConsumedOnlyForAcceptedSignedMode`, `SenderBoundAdmissionRequiresBinding`
- Properties: _none_
- Statement: In the bounded TLA+ perps submission auth-scope shadow model, accepted submissions require exactly one mode, signed-mode acceptance requires all signed checks, sender-bound mode never consumes a nonce, nonce consumption occurs only for accepted signed mode, and sender-bound admission requires binding.

### `ZenoGraphHostLocalAcceptance`

- Claim: `tla:zenograph_host_local_acceptance:accepted_only_execution_visibility`
- Module: `formal/tla/ZenoGraphHostLocalAcceptance.tla`
- Config: `formal/tla/ZenoGraphHostLocalAcceptance.cfg`
- Invariants: `TypeOK`, `AcceptedRequiresValidValidation`, `ExecutionVisibleOnlyIfAccepted`, `UnknownOrInvalidNeverVisible`, `RejectAndProposalFailClosed`
- Properties: _none_
- Statement: In the bounded TLA+ ZenoGraph host/local acceptance shadow model, accepted facts require valid local validation, execution-visible facts are visible only after local acceptance, and proposal/unknown/invalid/reject paths remain fail-closed.

### `ZenoSdkWalletSyncCheckpoint`

- Claim: `tla:zeno_sdk_wallet_sync_checkpoint:no_rollback_or_same_height_drift`
- Module: `formal/tla/ZenoSdkWalletSyncCheckpoint.tla`
- Config: `formal/tla/ZenoSdkWalletSyncCheckpoint.cfg`
- Invariants: `TypeOK`, `RejectedDoesNotMutateState`, `AcceptedRequiresValidBundle`, `AcceptedRequiresValidPriorState`, `AcceptedNeverRollsBack`, `AcceptedKeepsChainStableAfterInitialSync`, `AcceptedSameHeightCannotDrift`, `AcceptedStateMatchesCandidate`
- Properties: _none_
- Statement: In the bounded TLA+ Zeno SDK wallet-sync checkpoint shadow model, accepted updates require a validated checkpoint bundle, accepted updates from an existing state require a valid current-state hash, checkpoint height never decreases, chain id cannot change after initial sync, same-height accepted updates cannot change app/checkpoint commitments, and rejected updates do not mutate wallet-sync state.

## Liveness

### `ExactOutAdaptiveBuilderCompetition`

- Claim: `tla:exact_out_adaptive_builder_competition:fair_resolution`
- Module: `formal/tla/ExactOutAdaptiveBuilderCompetition.tla`
- Config: `formal/tla/ExactOutAdaptiveBuilderCompetition.cfg`
- Invariants: `TypeOK`, `QueueCoherent`, `BranchCoherent`
- Properties: `FairImpliesBuilderCompetitionEventuallyResolves`, `FairImpliesCheapHeadWithoutRemainingPreemptEventuallyReturnsSuccess`, `FairImpliesFallbackHeadWithoutRemainingPreemptEventuallyReturnsSuccess`, `FairImpliesNoPathHeadWithoutRemainingPreemptEventuallyFailsExplicitly`
- Statement: In the bounded TLA+ exact-out adaptive builder-competition model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `BUILDER_PREEMPT_BUDGET_MAX = 2`), under strong fairness of non-target dequeue and weak fairness of adaptive head-service actions, a target exact-out request under bounded arrivals ahead and bounded head preemption is eventually resolved; once preemption budget is exhausted, cheap-success heads eventually return success, fallback-required heads with fallback availability eventually return success, and heads with no available path eventually fail explicitly with reason.

### `ExactOutAdaptiveBuilderReorgQueue`

- Claim: `tla:exact_out_adaptive_builder_reorg_queue:fair_re_resolution`
- Module: `formal/tla/ExactOutAdaptiveBuilderReorgQueue.tla`
- Config: `formal/tla/ExactOutAdaptiveBuilderReorgQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`, `BranchCoherent`
- Properties: `FairImpliesBuilderReorgEventuallyResolves`, `FairImpliesCheapHeadWithoutRemainingPreemptEventuallyEntersSuccessPending`, `FairImpliesFallbackHeadWithoutRemainingPreemptEventuallyEntersSuccessPending`, `FairImpliesSuccessPendingEventuallyFinalizesOrRollsBack`, `FairImpliesNoPathHeadWithoutRemainingPreemptEventuallyFailsExplicitly`
- Statement: In the bounded TLA+ exact-out adaptive builder-reorg queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `BUILDER_PREEMPT_BUDGET_MAX = 1`, `REORG_BUDGET_MAX = 1`), under strong fairness of non-target dequeue and weak fairness of adaptive head-service/finalize actions, a target exact-out request under bounded arrivals ahead, bounded head preemption, and at most one post-success rollback is eventually resolved; once preemption budget is exhausted, cheap-success and fallback-success heads eventually enter success-pending, pending successes eventually finalize or roll back for bounded re-resolution, and no-path heads eventually fail explicitly with reason.

### `ExactOutAdaptiveFeePriorityQueue`

- Claim: `tla:exact_out_adaptive_fee_priority_queue:fair_resolution`
- Module: `formal/tla/ExactOutAdaptiveFeePriorityQueue.tla`
- Config: `formal/tla/ExactOutAdaptiveFeePriorityQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`, `PriorityCoherent`, `BranchCoherent`
- Properties: `FairImpliesFeePriorityEventuallyResolves`, `FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves`, `FairImpliesCheapHeadWithoutRemainingPriorityPressureEventuallyReturnsSuccess`, `FairImpliesFallbackHeadWithoutRemainingPriorityPressureEventuallyReturnsSuccess`, `FairImpliesNoPathHeadWithoutRemainingPriorityPressureEventuallyFailsExplicitly`
- Statement: In the bounded TLA+ exact-out adaptive fee-priority queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `HIGHER_PRIORITY_BUDGET_MAX = 2`, `TARGET_FEE_BUMP_BUDGET_MAX = 2`), under strong fairness of non-target dequeue and weak fairness of head-service and target fee-bump actions, a target exact-out request under bounded arrivals ahead and bounded higher-priority head preemption is eventually resolved; a target with remaining fee-bump budget eventually consumes that budget or resolves, cheap-success and fallback-success heads with no remaining priority pressure eventually return success, and no-path heads with no remaining priority pressure eventually fail explicitly with reason.

### `ExactOutAdaptiveFeePriorityReorgQueue`

- Claim: `tla:exact_out_adaptive_fee_priority_reorg_queue:fair_re_resolution`
- Module: `formal/tla/ExactOutAdaptiveFeePriorityReorgQueue.tla`
- Config: `formal/tla/ExactOutAdaptiveFeePriorityReorgQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`, `PriorityCoherent`, `BranchCoherent`
- Properties: `FairImpliesFeePriorityReorgEventuallyResolves`, `FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves`, `FairImpliesCheapHeadWithoutRemainingPriorityPressureEventuallyEntersSuccessPending`, `FairImpliesFallbackHeadWithoutRemainingPriorityPressureEventuallyEntersSuccessPending`, `FairImpliesSuccessPendingEventuallyFinalizesOrRollsBack`, `FairImpliesNoPathHeadWithoutRemainingPriorityPressureEventuallyFailsExplicitly`
- Statement: In the bounded TLA+ exact-out adaptive fee-priority reorg queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `HIGHER_PRIORITY_BUDGET_MAX = 1`, `TARGET_FEE_BUMP_BUDGET_MAX = 2`, `REORG_BUDGET_MAX = 1`), under strong fairness of non-target dequeue and weak fairness of head-service, target fee-bump, and finalize actions, a target exact-out request under bounded arrivals ahead, bounded higher-priority head preemption, and at most one post-success rollback is eventually resolved; a target with remaining fee-bump budget eventually consumes that budget or resolves, cheap-success and fallback-success heads with no remaining priority pressure eventually enter success-pending, pending successes eventually finalize or roll back for bounded re-resolution, and no-path heads with no remaining priority pressure eventually fail explicitly with reason.

### `ExactOutAdaptiveIngressQueue`

- Claim: `tla:exact_out_adaptive_ingress_queue:fair_resolution`
- Module: `formal/tla/ExactOutAdaptiveIngressQueue.tla`
- Config: `formal/tla/ExactOutAdaptiveIngressQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`, `BranchCoherent`
- Properties: `FairImpliesPendingTargetEventuallyResolves`, `FairImpliesCheapHeadEventuallyReturnsSuccess`, `FairImpliesFallbackHeadEventuallyReturnsSuccess`, `FairImpliesNoPathHeadEventuallyFailsExplicitly`
- Statement: In the bounded TLA+ exact-out adaptive ingress queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`), under strong fairness of non-target dequeue and weak fairness of adaptive head-service actions, a target exact-out request under bounded arrivals ahead is eventually resolved; cheap-success heads eventually return success, fallback-required heads with fallback availability eventually return success, and heads with no available path eventually fail explicitly with reason.

### `ExactOutAdaptiveLiveness`

- Claim: `tla:exact_out_adaptive_liveness:request_resolves`
- Module: `formal/tla/ExactOutAdaptiveLiveness.tla`
- Config: `formal/tla/ExactOutAdaptiveLiveness.cfg`
- Invariants: `TypeOK`, `BranchCoherent`
- Properties: `FairImpliesPendingRequestEventuallyResolves`
- Statement: In the bounded TLA+ exact-out adaptive control model, under weak fairness of cheap-path and fallback resolution actions, a pending request is eventually resolved either by success or by explicit failure, with cheap-path attempt preceding repaired fallback.

### `ExactOutAdaptiveSingleReorgQueue`

- Claim: `tla:exact_out_adaptive_single_reorg_queue:fair_re_resolution`
- Module: `formal/tla/ExactOutAdaptiveSingleReorgQueue.tla`
- Config: `formal/tla/ExactOutAdaptiveSingleReorgQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`, `BranchCoherent`
- Properties: `FairImpliesSingleReorgEventuallyResolves`, `FairImpliesCheapHeadEventuallyEntersSuccessPending`, `FairImpliesFallbackHeadEventuallyEntersSuccessPending`, `FairImpliesSuccessPendingEventuallyFinalizesOrRollsBack`, `FairImpliesNoPathHeadEventuallyFailsExplicitly`
- Statement: In the bounded TLA+ exact-out adaptive single-reorg queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `REORG_BUDGET_MAX = 1`), under strong fairness of non-target dequeue and weak fairness of adaptive head-service/finalize actions, a target exact-out request with at most one post-success rollback is eventually resolved; cheap-success and fallback-success heads eventually enter success-pending, pending successes eventually finalize or roll back for bounded re-resolution, and no-path heads eventually fail explicitly with reason.

### `OracleRecoveryLifecycle`

- Claim: `tla:oracle_recovery_lifecycle:fair_reenable_or_block`
- Module: `formal/tla/OracleRecoveryLifecycle.tla`
- Config: `formal/tla/OracleRecoveryLifecycle.cfg`
- Invariants: `TypeOK`, `BlockedAbsorbing`, `StaleBlocksRisky`
- Properties: `FairImpliesEventuallyFreshOrBlocked`, `FairImpliesHealthyRequestEventuallyResolved`
- Statement: In the bounded TLA+ oracle-recovery model (`EPOCH_MAX = 4`, `MAX_STALE = 1`), under weak fairness of oracle update, sync repair, and permanent-block actions plus strong fairness of risky-op re-enable, stale unblocked oracle state eventually becomes fresh or permanently blocked, and any requested risky action in a healthy oracle world is eventually resolved by re-enable or permanent block.

### `PerpEpochScheduler`

- Claim: `tla:perp_epoch_scheduler:terminates_each_epoch`
- Module: `formal/tla/PerpEpochScheduler.tla`
- Config: `formal/tla/PerpEpochScheduler.cfg`
- Invariants: `TypeOK`
- Properties: `FairImpliesEventuallyPublishes`, `FairImpliesEventuallySettles`, `FairImpliesPublishedEventuallySettles`
- Statement: In the bounded TLA+ scheduler model (`EPOCH_MAX = 3`), under weak fairness of publish and settle actions, every advanced unsettled epoch is eventually published and eventually settled (no stuck-between-phases scheduler behavior on the modeled control path).

### `PerpLiquidationBoundedOpenIngress`

- Claim: `tla:perp_liquidation_bounded_open_ingress:resolves_or_blocks`
- Module: `formal/tla/PerpLiquidationBoundedOpenIngress.tla`
- Config: `formal/tla/PerpLiquidationBoundedOpenIngress.cfg`
- Invariants: `TypeOK`, `GuardConsistent`
- Properties: `FairImpliesPendingQueueEventuallyResolves`, `FairImpliesSafePendingWithoutFurtherArrivalsEventuallyDrains`, `FairImpliesUnsafePendingEventuallyBlocks`
- Statement: In the bounded TLA+ liquidation bounded-open-ingress model (`MAX_QUEUE = 4`, `MAX_PER_BLOCK = 2`, `ARRIVAL_BUDGET_MAX = 2`), under strong fairness of liquidation processing and weak fairness of block advance and breaker actions, a pending queue with bounded arrivals eventually resolves by draining to zero or tripping the breaker; once arrivals are exhausted, safe pending queues drain, and unsafe pending queues block.

### `PerpLiquidationBuilderReorgQueue`

- Claim: `tla:perp_liquidation_builder_reorg_queue:resolves_or_blocks`
- Module: `formal/tla/PerpLiquidationBuilderReorgQueue.tla`
- Config: `formal/tla/PerpLiquidationBuilderReorgQueue.cfg`
- Invariants: `TypeOK`, `GuardConsistent`
- Properties: `FairImpliesBuilderReorgEventuallyResolves`, `FairImpliesProcessedPendingEventuallyFinalizesOrRollsBack`, `FairImpliesSafePendingWithoutRemainingAdversaryEventuallyDrains`, `FairImpliesUnsafePendingEventuallyBlocks`
- Statement: In the bounded TLA+ liquidation builder-reorg model (`MAX_QUEUE = 4`, `MAX_PER_BLOCK = 2`, `ARRIVAL_BUDGET_MAX = 2`, `BUILDER_PREEMPT_BUDGET_MAX = 1`, `REORG_BUDGET_MAX = 1`), under strong fairness of liquidation processing and weak fairness of finalize, block-advance, and breaker actions, a pending queue with bounded arrivals, bounded external capacity preemption, and at most one rollback of a processed liquidation eventually resolves by draining to zero or tripping the breaker; processed liquidations eventually finalize or roll back, once adversary budgets are exhausted safe pending queues drain, and unsafe pending queues block.

### `PerpLiquidationQueueDrain`

- Claim: `tla:perp_liquidation_queue_drain:resolves_or_blocks`
- Module: `formal/tla/PerpLiquidationQueueDrain.tla`
- Config: `formal/tla/PerpLiquidationQueueDrain.cfg`
- Invariants: `TypeOK`, `GuardConsistent`
- Properties: `FairImpliesPendingQueueEventuallyResolves`, `FairImpliesSafePendingEventuallyDrains`, `FairImpliesUnsafePendingEventuallyBlocks`
- Statement: In the bounded TLA+ liquidation-queue model (`MAX_QUEUE = 3`, `MAX_PER_BLOCK = 2`), under strong fairness of liquidation processing and weak fairness of block advance and breaker actions, a pending closed queue eventually resolves by draining to zero or tripping the breaker; safe proof-gated queues drain, unsafe queues block.

### `PerpSubmissionBuilderCompetition`

- Claim: `tla:perp_submission_builder_competition:fair_resolution`
- Module: `formal/tla/PerpSubmissionBuilderCompetition.tla`
- Config: `formal/tla/PerpSubmissionBuilderCompetition.cfg`
- Invariants: `TypeOK`, `QueueCoherent`
- Properties: `FairImpliesBuilderCompetitionEventuallyResolves`, `FairImpliesAdmissibleHeadWithoutRemainingPreemptEventuallyAccepts`, `FairImpliesInadmissibleHeadWithoutRemainingPreemptEventuallyRejects`
- Statement: In the bounded TLA+ perps submission builder-competition model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `BUILDER_PREEMPT_BUDGET_MAX = 2`), under strong fairness of non-target dequeue and weak fairness of accept/reject-at-head actions, a target submission under bounded arrivals ahead and bounded head preemption is eventually resolved; once preemption budget is exhausted, admissible head targets eventually accept and inadmissible head targets reject with reason.

### `PerpSubmissionBuilderReorgQueue`

- Claim: `tla:perp_submission_builder_reorg_queue:fair_re_resolution`
- Module: `formal/tla/PerpSubmissionBuilderReorgQueue.tla`
- Config: `formal/tla/PerpSubmissionBuilderReorgQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`
- Properties: `FairImpliesBuilderReorgEventuallyResolves`, `FairImpliesAdmissibleHeadWithoutRemainingPreemptEventuallyAccepts`, `FairImpliesAcceptedPendingEventuallyFinalizesOrRollsBack`, `FairImpliesInadmissibleHeadWithoutRemainingPreemptEventuallyRejects`
- Statement: In the bounded TLA+ perps submission builder-reorg queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `BUILDER_PREEMPT_BUDGET_MAX = 1`, `REORG_BUDGET_MAX = 1`), under strong fairness of non-target dequeue and weak fairness of accept/finalize/reject actions, a target submission under bounded arrivals ahead, bounded head preemption, and at most one post-accept rollback is eventually resolved; once preemption budget is exhausted, admissible head targets eventually accept, accepted-pending targets eventually finalize or roll back for bounded re-resolution, and inadmissible head targets eventually reject with reason.

### `PerpSubmissionFeePriorityQueue`

- Claim: `tla:perp_submission_fee_priority_queue:fair_resolution`
- Module: `formal/tla/PerpSubmissionFeePriorityQueue.tla`
- Config: `formal/tla/PerpSubmissionFeePriorityQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`, `PriorityCoherent`
- Properties: `FairImpliesFeePriorityEventuallyResolves`, `FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves`, `FairImpliesAdmissibleHeadWithoutRemainingPriorityPressureEventuallyAccepts`, `FairImpliesInadmissibleHeadEventuallyRejects`
- Statement: In the bounded TLA+ perps submission fee-priority queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `HIGHER_PRIORITY_BUDGET_MAX = 2`, `TARGET_FEE_BUMP_BUDGET_MAX = 2`), under strong fairness of non-target dequeue and weak fairness of head-service and target fee-bump actions, a target submission under bounded arrivals ahead and bounded higher-priority head preemption is eventually resolved; a target with remaining fee-bump budget eventually consumes that budget or resolves, admissible head targets with no remaining priority pressure eventually accept, and inadmissible head targets reject with reason.

### `PerpSubmissionIngressQueue`

- Claim: `tla:perp_submission_ingress_queue:fair_resolution`
- Module: `formal/tla/PerpSubmissionIngressQueue.tla`
- Config: `formal/tla/PerpSubmissionIngressQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`
- Properties: `FairImpliesPendingTargetEventuallyResolves`, `FairImpliesAdmissibleHeadEventuallyAccepts`, `FairImpliesInadmissibleHeadEventuallyRejects`
- Statement: In the bounded TLA+ perps submission-ingress queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`), under strong fairness of non-target dequeue and weak fairness of accept/reject-at-head actions, a target perps submission under bounded arrivals ahead is eventually resolved; admissible head targets accept, inadmissible head targets reject with reason.

### `PerpSubmissionSingleReorgQueue`

- Claim: `tla:perp_submission_single_reorg_queue:fair_re_resolution`
- Module: `formal/tla/PerpSubmissionSingleReorgQueue.tla`
- Config: `formal/tla/PerpSubmissionSingleReorgQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`
- Properties: `FairImpliesSingleReorgEventuallyResolves`, `FairImpliesAdmissibleHeadEventuallyAccepts`, `FairImpliesAcceptedPendingEventuallyFinalizesOrRollsBack`, `FairImpliesInadmissibleHeadEventuallyRejects`
- Statement: In the bounded TLA+ perps submission single-reorg queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `REORG_BUDGET_MAX = 1`), under strong fairness of non-target dequeue and weak fairness of accept/finalize/reject-at-head actions, a target submission with at most one post-accept rollback is eventually resolved; admissible head targets eventually accept, accepted submissions eventually either finalize or roll back for bounded re-resolution, and inadmissible head targets reject with reason.

### `SettlementAttestationGovernance`

- Claim: `tla:settlement_attestation_governance:governed_policy_activation`
- Module: `formal/tla/SettlementAttestationGovernance.tla`
- Config: `formal/tla/SettlementAttestationGovernance.cfg`
- Invariants: `TypeOK`, `AcceptedSettlementRequiresActiveGovernedPolicy`, `RevokedPolicyRejectsFutureSettlement`, `NoRetroactiveEpochDriftOnAcceptedSettlement`
- Properties: `FairImpliesApprovedPolicyEventuallyActivates`
- Statement: In the bounded TLA+ settlement-attestation governance model (`SIGNERS = {0,1}`, `SOURCES = {0,1}`), accepted settlements require an active approved, timelocked, multisig-backed, non-revoked policy snapshot with enough observed signers and sources; revoked active policy blocks future settlement acceptance; accepted settlements cannot drift away from the active policy epoch; and under weak fairness, an approved pending policy with an elapsed timelock eventually activates.

### `SettlementSignerRegistryTauBridge`

- Claim: `tla:settlement_signer_registry_tau_bridge:bound_snapshot_and_anchor`
- Module: `formal/tla/SettlementSignerRegistryTauBridge.tla`
- Config: `formal/tla/SettlementSignerRegistryTauBridge.cfg`
- Invariants: `TypeOK`, `AcceptedRequiresBoundSnapshot`, `DriftedSnapshotBlocksAcceptance`, `DriftedAnchorBlocksAcceptance`
- Properties: `FairReadyRequestEventuallyAccepts`, `FairBindingMismatchEventuallyRejects`, `FairBridgeReadyEventuallyChecksPolicyBinding`, `FairPolicyBoundArtifactsEventuallyCheckProofPath`, `FairCleanArtifactsEventuallyCheckPolicyBinding`, `FairProofPathEventuallyResolves`
- Statement: In the bounded TLA+ Tau-native settlement signer-registry bridge model, accepted requests require a request-bound registry snapshot and chain anchor, drifted snapshots or anchors block acceptance, and under weak fairness ready requests eventually accept while visible binding mismatches and unavailable proof paths eventually resolve by rejection or proof-path checks.

### `SettlementWitnessBoundedOpenIngress`

- Claim: `tla:settlement_witness_bounded_open_ingress:fair_resolution`
- Module: `formal/tla/SettlementWitnessBoundedOpenIngress.tla`
- Config: `formal/tla/SettlementWitnessBoundedOpenIngress.cfg`
- Invariants: `TypeOK`, `QueueCoherent`
- Properties: `FairImpliesBoundedOpenIngressEventuallyResolves`, `FairImpliesAdmissibleHeadEventuallyIncludes`, `FairImpliesInadmissibleHeadEventuallyRejects`
- Statement: In the bounded TLA+ settlement witness open-ingress model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`), under strong fairness of non-target dequeue and weak fairness of include/reject-at-head actions, a target witness under bounded adversarial arrivals ahead is eventually resolved; admissible head targets include, inadmissible head targets reject with reason.

### `SettlementWitnessBuilderCompetition`

- Claim: `tla:settlement_witness_builder_competition:fair_resolution`
- Module: `formal/tla/SettlementWitnessBuilderCompetition.tla`
- Config: `formal/tla/SettlementWitnessBuilderCompetition.cfg`
- Invariants: `TypeOK`, `QueueCoherent`
- Properties: `FairImpliesBuilderCompetitionEventuallyResolves`, `FairImpliesAdmissibleHeadWithoutRemainingPreemptEventuallyIncludes`, `FairImpliesInadmissibleHeadWithoutRemainingPreemptEventuallyRejects`
- Statement: In the bounded TLA+ settlement witness builder-competition model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `BUILDER_PREEMPT_BUDGET_MAX = 2`), under strong fairness of non-target dequeue and weak fairness of include/reject-at-head actions, a target witness under bounded arrivals ahead and bounded head preemption is eventually resolved; once preemption budget is exhausted, admissible head targets eventually include and inadmissible head targets reject with reason.

### `SettlementWitnessBuilderReorgQueue`

- Claim: `tla:settlement_witness_builder_reorg_queue:fair_re_resolution`
- Module: `formal/tla/SettlementWitnessBuilderReorgQueue.tla`
- Config: `formal/tla/SettlementWitnessBuilderReorgQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`
- Properties: `FairImpliesBuilderReorgEventuallyResolves`, `FairImpliesAdmissibleHeadWithoutRemainingPreemptEventuallyIncludes`, `FairImpliesIncludedPendingEventuallyFinalizesOrRollsBack`, `FairImpliesInadmissibleHeadWithoutRemainingPreemptEventuallyRejects`
- Statement: In the bounded TLA+ settlement witness builder-reorg queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `BUILDER_PREEMPT_BUDGET_MAX = 1`, `REORG_BUDGET_MAX = 1`), under strong fairness of non-target dequeue and weak fairness of include/finalize/reject actions, a target settlement witness under bounded arrivals ahead, bounded head preemption, and at most one post-inclusion rollback is eventually resolved; once preemption budget is exhausted, admissible head targets eventually include, included-pending targets eventually finalize or roll back for bounded re-resolution, and inadmissible head targets eventually reject with reason.

### `SettlementWitnessFeePriorityQueue`

- Claim: `tla:settlement_witness_fee_priority_queue:fair_resolution`
- Module: `formal/tla/SettlementWitnessFeePriorityQueue.tla`
- Config: `formal/tla/SettlementWitnessFeePriorityQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`, `PriorityCoherent`
- Properties: `FairImpliesFeePriorityEventuallyResolves`, `FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves`, `FairImpliesAdmissibleHeadWithoutRemainingPriorityPressureEventuallyIncludes`, `FairImpliesInadmissibleHeadEventuallyRejects`
- Statement: In the bounded TLA+ settlement witness fee-priority queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `HIGHER_PRIORITY_BUDGET_MAX = 2`, `TARGET_FEE_BUMP_BUDGET_MAX = 2`), under strong fairness of non-target dequeue and weak fairness of head-service and target fee-bump actions, a target witness under bounded arrivals ahead and bounded higher-priority head preemption is eventually resolved; a target with remaining fee-bump budget eventually consumes that budget or resolves, admissible head targets with no remaining priority pressure eventually include, and inadmissible head targets reject with reason.

### `SettlementWitnessFeePriorityReorgQueue`

- Claim: `tla:settlement_witness_fee_priority_reorg_queue:fair_re_resolution`
- Module: `formal/tla/SettlementWitnessFeePriorityReorgQueue.tla`
- Config: `formal/tla/SettlementWitnessFeePriorityReorgQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`, `PriorityCoherent`
- Properties: `FairImpliesFeePriorityReorgEventuallyResolves`, `FairImpliesTargetWithRemainingFeeBumpBudgetEventuallyBumpsOrResolves`, `FairImpliesAdmissibleHeadWithoutRemainingPriorityPressureEventuallyIncludes`, `FairImpliesIncludedPendingEventuallyFinalizesOrRollsBack`, `FairImpliesInadmissibleHeadEventuallyRejects`
- Statement: In the bounded TLA+ settlement witness fee-priority reorg queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `HIGHER_PRIORITY_BUDGET_MAX = 1`, `TARGET_FEE_BUMP_BUDGET_MAX = 2`, `REORG_BUDGET_MAX = 1`), under strong fairness of non-target dequeue and weak fairness of head-service, target fee-bump, and finalize actions, a target witness under bounded arrivals ahead, bounded higher-priority head preemption, and at most one post-inclusion rollback is eventually resolved; a target with remaining fee-bump budget eventually consumes that budget or resolves, admissible head targets with no remaining priority pressure eventually include, included-pending targets eventually finalize or roll back for bounded re-resolution, and inadmissible head targets reject with reason.

### `SettlementWitnessInclusionQueue`

- Claim: `tla:settlement_witness_inclusion_queue:fair_dequeue`
- Module: `formal/tla/SettlementWitnessInclusionQueue.tla`
- Config: `formal/tla/SettlementWitnessInclusionQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`
- Properties: `FairImpliesAcceptedTargetEventuallyResolves`, `FairImpliesAdmissibleHeadEventuallyIncludes`, `FairImpliesInadmissibleHeadEventuallyRejects`
- Statement: In the bounded TLA+ settlement witness inclusion-queue model (`MAX_QUEUE = 4`), under strong fairness of non-target dequeue and weak fairness of include/reject-at-head actions, an accepted target witness in a closed finite queue is eventually resolved; admissible head targets include, inadmissible head targets reject with reason.

### `SettlementWitnessLifecycle`

- Claim: `tla:settlement_witness_lifecycle:accepted_resolves_before_expiry`
- Module: `formal/tla/SettlementWitnessLifecycle.tla`
- Config: `formal/tla/SettlementWitnessLifecycle.cfg`
- Invariants: `TypeOK`, `ResolutionConsistent`
- Properties: `FairImpliesAcceptedBeforeExpiryEventuallyResolved`
- Statement: In the bounded TLA+ settlement witness lifecycle model (`TIME_MAX = 4`, `EXPIRY = 2`), under weak fairness of settle, invalid-reject, and expired-reject actions, any witness accepted before expiry is eventually resolved by settlement or rejection with an explicit reason.

### `SettlementWitnessSingleReorgQueue`

- Claim: `tla:settlement_witness_single_reorg_queue:fair_re_resolution`
- Module: `formal/tla/SettlementWitnessSingleReorgQueue.tla`
- Config: `formal/tla/SettlementWitnessSingleReorgQueue.cfg`
- Invariants: `TypeOK`, `QueueCoherent`
- Properties: `FairImpliesSingleReorgEventuallyResolves`, `FairImpliesAdmissibleHeadEventuallyIncludes`, `FairImpliesIncludedPendingEventuallyFinalizesOrRollsBack`, `FairImpliesInadmissibleHeadEventuallyRejects`
- Statement: In the bounded TLA+ settlement witness single-reorg queue model (`MAX_QUEUE = 5`, `ARRIVAL_BUDGET_MAX = 2`, `REORG_BUDGET_MAX = 1`), under strong fairness of non-target dequeue and weak fairness of include/finalize/reject-at-head actions, a target witness with at most one post-inclusion rollback is eventually resolved; admissible head targets eventually include, included targets eventually either finalize or roll back for bounded re-resolution, and inadmissible head targets reject with reason.

### `TauStateAppHashProvenanceBridge`

- Claim: `tla:tau_state_app_hash_provenance_bridge:loader_acceptance_binding`
- Module: `formal/tla/TauStateAppHashProvenanceBridge.tla`
- Config: `formal/tla/TauStateAppHashProvenanceBridge.cfg`
- Invariants: `TypeOK`, `AcceptedStateRequiresLoaderOK`, `StrongBindingMismatchStateBlocksAcceptance`, `MissingTauTransportStateBlocksAcceptance`
- Properties: `AcceptedRequiresLoaderOK`, `StrongBindingMismatchBlocksAcceptance`, `MissingTauTransportBlocksAcceptance`, `FairCleanReadyStateEventuallyAccepts`, `FairVisibleStrongBindingFailureEventuallyRejects`, `FairMissingTauTransportEventuallyRejects`
- Statement: In the bounded TLA+ Tau-state/app-hash provenance bridge model, accepted loader requests require bridge payload checks, baseline provenance checks, state-proof error freedom, and the stronger Tau-state transport plus binding checks whenever strong binding is required; visible bridge, baseline, transport, or Tau-binding failures block acceptance and under weak fairness eventually resolve by rejection or acceptance when the clean ready state is reached.

### `TauStateAppHashStableWindow`

- Claim: `tla:tau_state_app_hash_stable_window:bounded_retry_resolution`
- Module: `formal/tla/TauStateAppHashStableWindow.tla`
- Config: `formal/tla/TauStateAppHashStableWindow.cfg`
- Invariants: `TypeOK`, `ReturnedRequiresStableWindow`, `StableWindowFoundRequiresReturned`, `StrongBindingWithoutTauStabilityBlocksReturn`
- Properties: `FairUnstabilizableWindowEventuallyRejects`
- Statement: In the bounded TLA+ Tau-state app-hash stable-window model, returned loader output requires a stable proof/app window and, when strong binding is required, a stable Tau-state observation; finding a stable window implies a returned result; strong binding without Tau stability blocks return; and under weak fairness an unstabilizable window eventually rejects after the bounded retry budget is exhausted.

## Notes

- These are bounded TLC model checks, not unbounded proofs.
- Fairness assumptions and model bounds are part of each claim statement and must not be widened implicitly.
- The generated summary is only as strong as the corresponding `.tla`, `.cfg`, and release-checked claim entry.

