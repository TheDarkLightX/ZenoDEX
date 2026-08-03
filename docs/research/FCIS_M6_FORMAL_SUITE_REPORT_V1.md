# FCIS M6 formal suite report v1

## Result

- Verdict: `PASS_BOUNDED_INDEPENDENT_REPLAY`
- Models: 13
- Reachable states: 1031
- Enabled transitions: 7496
- Formal invariants: 76
- Named adversarial mutants killed: 83 of 83
- ESSO dual-solver receipt: **not produced in this environment**; the committed gate must be rerun with pinned Z3 and cvc5.

## Model sizes

| Model | Reachable states | Enabled transitions | Base violations |
| --- | ---: | ---: | ---: |
| `fcis_m6_atomic_publication_v1` | 7 | 16 | 0 |
| `fcis_m6_history_fixed_point_v1` | 513 | 4368 | 0 |
| `fcis_m6_managed_asset_issuance_v1` | 20 | 152 | 0 |
| `fcis_m6_migration_writer_v1` | 18 | 32 | 0 |
| `fcis_m6_no_bypass_v1` | 77 | 770 | 0 |
| `fcis_m6_nonce_retry_classifier_v1` | 12 | 64 | 0 |
| `fcis_m6_oracle_risk_gate_v1` | 27 | 159 | 0 |
| `fcis_m6_outbox_delivery_v1` | 7 | 23 | 0 |
| `fcis_m6_promotion_subject_v1` | 83 | 652 | 0 |
| `fcis_m6_proof_context_v1` | 23 | 273 | 0 |
| `fcis_m6_reopen_reauthorization_v1` | 69 | 288 | 0 |
| `fcis_m6_value_flow_kernel_v1` | 126 | 539 | 0 |
| `fcis_m6_zenoledger_tau_continuity_v1` | 49 | 160 | 0 |

## Adversarial refinement history

The first bounded replay was not accepted. It exposed four specification weaknesses:

1. the one-commit publication model allowed a new head authorization after terminal commit;
2. promotion evidence could be changed after promotion;
3. authority switch without quiescence was not represented by a state predicate strong enough to refute the phase skip;
4. the no-bypass model did not bind the commit-port capability to the currently selected entrypoint.

The models were revised by making terminal evidence immutable, adding a quiescence ghost/premise, and binding the commit-port entrypoint identity. The second pass killed all original mutants. A further invariant-coverage pass added retained mutants until every one of the original 42 invariants killed at least one named mutant. A second completeness review added separate nonce/retry, canonical-history, proof-context, and oracle-risk models rather than expanding the existing models.

The PR review then found two packet-level defects: a stale source manifest and a replay checker whose default pretty-printed output did not reproduce the committed compact evidence bytes. The checker now emits one canonical compact representation, checks the committed evidence by default, and requires explicit `--output` for regeneration. The same review found that the suite treated Tau as a possible durability authority and omitted the required ZenoLedger continuity lane. The thirteenth model freezes ZenoLedger as the canonical economic ledger, treats authenticated Tau integration as optional, and covers Tau unavailability, censorship, current-checkpoint rejoin, and forbidden Tau-driven ledger rewrites. The repaired campaign contains 83 mutants, and each of the 76 invariants has at least one retained killing mutant.

## Final negative classes

- `VF_TRANSFER_MISSING_CREDIT` -> `AssetQuantityConservation`
- `VF_ESCROW_LOCK_MISSING_DEBIT` -> `AssetQuantityConservation`
- `VF_MINT_WITHOUT_ISSUANCE` -> `AssetQuantityConservation`
- `VF_BURN_WITHOUT_HOLDING_DEBIT` -> `AssetQuantityConservation`
- `MA_GENERIC_MINT_ENABLED` -> `DebtEqualsSupplyPlusClaim`
- `MA_GENERIC_BURN_ENABLED` -> `DebtEqualsSupplyPlusClaim`
- `MA_BORROW_DEBT_OMITTED` -> `DebtEqualsSupplyPlusClaim`
- `MA_CLAIM_REALIZED_WITHOUT_CLAIM_DEBIT` -> `DebtEqualsSupplyPlusClaim`
- `AP_STATE_ONLY_WITHOUT_HISTORY` -> `history_publishedIffCommit`
- `AP_NO_ECONOMIC_CERTIFICATE` -> `economic_certificate_publishedIffCommit`
- `AP_PUBLISH_WITHOUT_VERIFICATION` -> `CommitRequiresVerifiedCandidate`
- `AP_AUTH_NOT_CONSUMED` -> `CommitConsumesHeadAuthorization`
- `RR_RESTART_RETAINS_AUTH` -> `AuthorizedOnlyAfterCanonicalOpen`
- `RR_GRANT_IGNORES_HEAD_EPOCH` -> `AuthorizedHeadIsCurrentReopenedHead`
- `RR_COMMIT_RETAINS_AUTH` -> `AuthorizedHeadIsCurrentReopenedHead`
- `RR_EPOCH_SWITCH_RETAINS_AUTH` -> `AuthorizedEpochIsCurrent`
- `OB_COMMIT_WITHOUT_OUTBOX` -> `OutboxIffCommitted`
- `OB_DELIVER_BEFORE_COMMIT` -> `DeliveryRequiresCommittedOutbox`
- `OB_ACK_FOREIGN_EFFECT` -> `AckBindsCommittedEffect`
- `OB_REDELIVERY_DUPLICATES_EFFECT` -> `AtMostOneSemanticEffect`
- `MW_QUIESCE_WITH_TARGET_WRITER` -> `QuiescedNoWriter`
- `MW_SWITCH_LEAVES_LEGACY_ENABLED` -> `NeverDualEnabledWriters`
- `MW_SWITCH_SKIPS_QUIESCENCE` -> `PostSwitchRequiresQuiescence`
- `MW_STALE_AUTH_SURVIVES_EPOCH` -> `AuthorizationEpochCurrent`
- `NB_VALUE_CHANGE_WITHOUT_PORT` -> `ValueChangeRequiresAttestedInventory`
- `NB_VALUE_CHANGE_WITHOUT_RECEIPT` -> `ValueChangeRequiresReceipt`
- `NB_SELECT_RETAINS_OLD_PORT` -> `ValueChangePortBindsSelectedEntrypoint`
- `PS_PROMOTE_WITHOUT_GATES` -> `PromotionRequiresAllFourGates`
- `PS_CROSS_SUBJECT_PROMOTION` -> `PromotionRequiresProofImplementationSubjectEquality`
- `AP_STATE_NOT_PUBLISHED` -> `state_publishedIffCommit`
- `AP_NULLIFIER_NOT_PUBLISHED` -> `nullifier_publishedIffCommit`
- `AP_RECEIPT_NOT_PUBLISHED` -> `receipt_publishedIffCommit`
- `AP_OUTBOX_NOT_PUBLISHED` -> `outbox_publishedIffCommit`
- `AP_EPOCH_NOT_PUBLISHED` -> `authority_epoch_publishedIffCommit`
- `AP_AUTH_ISSUANCE_NOT_RETAINED` -> `CommitRequiresIssuedAuthorization`
- `RR_REOPEN_WRONG_HEAD` -> `CanonicalOpenMatchesStoredHead`
- `OB_ACK_WITHOUT_DELIVERY` -> `AckRequiresDelivery`
- `OB_DELIVERY_WITHOUT_COUNT` -> `DeliveredIffOneSemanticEffect`
- `MW_PRE_SWITCH_TARGET_WRITER` -> `PreSwitchLegacyWriter`
- `MW_POST_SWITCH_LEGACY_WRITER` -> `PostSwitchTargetWriter`
- `MW_LEGACY_DISABLED_PRE_SWITCH` -> `LegacyWriterImpliesLegacyEnabled`
- `MW_TARGET_NOT_ENABLED` -> `TargetWriterImpliesTargetEnabled`
- `MW_DUAL_EQUALITY_ERASED_AT_SWITCH` -> `PostSwitchRequiresDualEquality`
- `MW_TRANSPORT_ERASED_AT_SWITCH` -> `PostSwitchRequiresTransportComplete`
- `NB_VALUE_CHANGE_WITHOUT_MOUNT` -> `ValueChangeRequiresMountedDeployment`
- `NB_VALUE_CHANGE_WITHOUT_UNIQUE_PORT` -> `ValueChangeRequiresUniqueCommitPort`
- `NB_RECEIPT_WITHOUT_VALUE_CHANGE` -> `ReceiptIffValueChange`
- `PS_PROOF_MOUNT_CROSS_LINEAGE` -> `PromotionRequiresProofMountSubjectEquality`
- `PS_PROOF_TEST_CROSS_LINEAGE` -> `PromotionRequiresProofTestSubjectEquality`
- `NR_COMMIT_COUNT_OMITTED` -> `CommittedIffOneCount`
- `NR_HEAD_NOT_ADVANCED` -> `HeadEqualsCommitCount`
- `NR_IDENTITY_NOT_SEALED` -> `CommittedIdentitySealed`
- `NR_NULLIFIER_NOT_CONSUMED` -> `CommittedNullifierConsumed`
- `NR_ABSENT_CLASS_WRONG` -> `AbsentRelationClassifiesNew`
- `NR_RETRY_CLASS_WRONG` -> `ExactRetryClassifiesAlready`
- `NR_COLLISION_CLASS_WRONG` -> `CollisionClassifiesRejection`
- `NR_STALE_CLASS_WRONG` -> `StaleRelationClassifiesStale`
- `HF_REMOVE_STATE_RETAINS_OPEN` -> `OpenRequiresStateRow`
- `HF_REMOVE_HISTORY_RETAINS_OPEN` -> `OpenRequiresHistoryRow`
- `HF_REMOVE_EVIDENCE_RETAINS_OPEN` -> `OpenRequiresEvidenceRow`
- `HF_REMOVE_NULLIFIER_RETAINS_OPEN` -> `OpenRequiresNullifierRow`
- `HF_REMOVE_RECEIPT_RETAINS_OPEN` -> `OpenRequiresReceiptRow`
- `HF_REMOVE_OUTBOX_RETAINS_OPEN` -> `OpenRequiresOutboxRow`
- `HF_REMOVE_AUTHORITY_RETAINS_OPEN` -> `OpenRequiresAuthorityRow`
- `HF_CROSSED_RELATION_RETAINS_OPEN` -> `OpenRequiresValidRelations`
- `HF_SURPLUS_ROW_RETAINS_OPEN` -> `OpenRequiresExactLayout`
- `HF_REOPEN_IGNORES_FIXED_POINT` -> `OpenRequiresFixedPoint`
- `HF_REENCODE_PARTIAL_LAYOUT` -> `FixedPointRequiresCompleteLayout`
- `PC_VERIFY_NO_RECEIPT` -> `AcceptedIffVerifierReceipt`
- `PC_ACCEPT_WITHOUT_REGISTRY` -> `AcceptedRequiresPinnedRegistry`
- `PC_ACCEPT_WITHOUT_PROOF` -> `AcceptedRequiresProofPresent`
- `PC_ACCEPT_FAULTY_CONTEXT` -> `AcceptedRequiresExactContext`
- `OR_ACCEPT_PENDING_RISK` -> `RiskIncreaseRequiresFinalFresh`
- `OR_ACCEPT_UNBOUND_REDUCE` -> `PriceDependentAcceptRequiresBoundContext`
- `OR_RISK_CHANGE_NO_CERT` -> `ValueChangeRequiresEconomicCertificate`
- `OR_REJECT_CHANGES_VALUE` -> `RejectHasNoValueChange`
- `ZT_TAU_REWRITES_LEDGER_HEAD` -> `LedgerHeadEqualsCommitCount`
- `ZT_OUTAGE_DISABLES_LEDGER_WRITER` -> `TauDisruptionPreservesLedgerWriter`
- `ZT_TAU_ANCHOR_ADVANCES_AHEAD` -> `TauAnchorNotAheadOfLedger`
- `ZT_COMMIT_RETAINS_CHECKPOINT_AUTH` -> `AuthenticatedCheckpointIsCurrent`
- `ZT_OUTAGE_RETAINS_TAU_AUTHORITY` -> `TauAuthorityRequiresAvailable`
- `ZT_COMMIT_RETAINS_TAU_AUTHORITY` -> `TauAuthorityRequiresCurrentAnchor`
- `ZT_ANCHOR_WITHOUT_CURRENT_CHECKPOINT` -> `TauAuthorityRequiresCurrentCheckpoint`

## Required solver gate

The hosted `FCIS M6 bounded formal assurance` workflow checks exact source hashes, canonical bounded replay bytes, the formal/runtime obligation matrix, focused tests, and the open Grade F boundary. It does not claim or fabricate a private ESSO receipt.

```bash
FCIS_REQUIRE_ESSO=1 ESSO_ROOT=external/ESSO tools/run_fcis_m6_formal_assurance_gate.sh
```

The gate must fail on solver disagreement, `UNKNOWN`, timeout, unsupported operations, a surviving mutant, an unreachable intended action, a reachable forbidden action, model/matrix drift, or a base invariant violation.

## Formal status

- The ESSO specifications and theorem statement are frozen candidates.
- Independent finite replay is reproducibly green.
- ZenoLedger is the canonical durability target; Tau is an optional authenticated integration and SQLite remains an unmounted conformance adapter.
- The abstract composition theorem remains `THEOREM_STATEMENT_FROZEN_PROOF_OPEN`.
- The 32 runtime projection identifiers are closed source obligations with status `DECLARED_ONLY_NO_RUNTIME_IMPLEMENTATION`; registry consistency is not Grade R evidence.
- Runtime projections, ATDD step definitions, concrete storage refinement, mounted inventory completeness, and production promotion remain open.
- No value movement or production authority is granted by this packet.
