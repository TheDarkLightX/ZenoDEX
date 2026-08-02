@fcis @m6 @formal_refinement
Feature: Mounted runtime refines the FCIS M6 formal safety suite
  Every authoritative value-moving runtime action must project to one enabled
  formal action, produce the same complete successor, and preserve the exact
  invariant set at one promotion subject.

  Background:
    Given one exact M6 promotion subject is pinned
    And the formal model roots and runtime projection version are pinned
    And the mounted publisher inventory is externally attested

  @model_fcis_m6_value_flow_kernel_v1
  Scenario Outline: Asset-flow runtime actions preserve quantity conservation
    Given a reachable runtime state projecting to "fcis_m6_value_flow_kernel_v1"
    When the mounted runtime executes a command mapped to "<formal_action>"
    Then the runtime decision equals the formal decision
    And the complete projected successor equals the formal successor
    And a rejection publishes no state or effect
    And "AssetQuantityConservation" holds

    Examples:
      | formal_action |
      | transfer_alice_to_bob |
      | escrow_lock |
      | escrow_release |
      | fee_charge |
      | external_delivery |
      | authorized_mint |
      | authorized_burn |

  @model_fcis_m6_managed_asset_issuance_v1
  Scenario Outline: Managed-asset runtime actions preserve debt and issuance identity
    Given the configured managed asset is excluded from every generic issuer
    And a reachable runtime state projects to "fcis_m6_managed_asset_issuance_v1"
    When the mounted runtime executes a command mapped to "<formal_action>"
    Then the complete projected successor equals the formal successor
    And "DebtEqualsSupplyPlusClaim" holds

    Examples:
      | formal_action |
      | protocol_borrow |
      | realize_protocol_claim |
      | repay_and_burn |
      | cancel_protocol_claim |
      | generic_transfer |

  @negative @managed_asset
  Scenario Outline: Generic issuers cannot alter a managed asset
    Given the asset is governed by the managed-asset policy
    When "<formal_action>" is attempted through any API, CLI, faucet, migration, or ledger route
    Then the runtime rejects before constructing a candidate
    And debt, supply, protocol claim, history, and outbox remain unchanged

    Examples:
      | formal_action |
      | generic_mint_managed_asset |
      | generic_burn_managed_asset |

  @model_fcis_m6_atomic_publication_v1 @crash
  Scenario Outline: Publication is all-or-nothing at every boundary
    Given a verifier-produced candidate and fresh current-head authorization
    And a crash is injected at "<crash_point>"
    When the actual mounted commit port attempts publication
    Then canonical reopen yields exact PRE, exact POST, or fail-closed rejection
    And no accepted layout contains a partial publication atom

    Examples:
      | crash_point |
      | before_transaction |
      | before_compare_and_swap |
      | after_compare_and_swap_check |
      | after_state_write |
      | after_history_write |
      | after_nullifier_write |
      | after_receipt_write |
      | after_economic_certificate_write |
      | after_outbox_write |
      | after_authority_epoch_write |
      | before_commit |
      | after_commit_before_response |

  @model_fcis_m6_reopen_reauthorization_v1
  Scenario Outline: Recovery never restores stale value-moving authority
    Given the process is in "<recovery_case>"
    When the mounted runtime reopens authoritative state
    Then no value-moving write capability exists
    And only a fresh token bound to the exact reopened head and current authority epoch can authorize a commit

    Examples:
      | recovery_case |
      | normal_restart |
      | crash_before_commit |
      | crash_after_commit |
      | corrupt_layout |
      | authority_epoch_changed |

  @model_fcis_m6_outbox_delivery_v1
  Scenario Outline: External delivery retains one semantic identity
    Given a committed outbox entry with a stable effect identity
    When "<delivery_case>" occurs
    Then every attempt uses the same effect identity and payload
    And at most one semantic effect is accepted by the destination
    And any local acknowledgment binds the committed effect and destination receipt

    Examples:
      | delivery_case |
      | first_delivery |
      | worker_crash_before_send |
      | worker_crash_after_send |
      | acknowledgment_transport_loss |
      | expired_lease_redelivery |
      | foreign_receipt_substitution |
      | payload_substitution |

  @model_fcis_m6_migration_writer_v1
  Scenario Outline: Migration preserves one authoritative writer
    Given the migration machine is in "<phase>"
    When a legacy writer, target writer, crash, restart, or stale token attempts a transition
    Then the result matches "fcis_m6_migration_writer_v1"
    And no reachable state has two enabled authoritative writers
    And authority switch is impossible before dual equality, complete transport, and quiescence

    Examples:
      | phase |
      | LEGACY |
      | SHADOW_REPLAY |
      | DUAL_CHECK |
      | QUIESCED |
      | AUTHORITY_SWITCH |
      | POST_SWITCH_VALIDATION |
      | LEGACY_DISABLED |

  @model_fcis_m6_no_bypass_v1
  Scenario Outline: Every mounted value-moving entrypoint traverses the unique commit port
    Given "<entrypoint>" is present in the anchored production inventory
    When it attempts any protected value change
    Then it consumes one verifier-produced candidate through the unique commit port
    And direct state, history, nullifier, receipt, outbox, and effect writes are denied

    Examples:
      | entrypoint |
      | API |
      | CLI |
      | ADMIN |
      | MIGRATION |
      | RECOVERY |
      | OUTBOX_WORKER |
      | LEDGER_HOST |

  @model_fcis_m6_promotion_subject_v1
  Scenario Outline: Evidence from different lineages cannot be accumulated
    Given the proof binds "<proof_subject>"
    And implementation, mount, or tests bind "<other_subject>"
    When M6 promotion is evaluated
    Then promotion is rejected unless every gate binds the same exact subject

    Examples:
      | proof_subject | other_subject |
      | SUBJECT_A | SUBJECT_B |
      | SUBJECT_B | SUBJECT_A |

  @model_fcis_m6_nonce_retry_classifier_v1
  Scenario Outline: Retry and transport uncertainty preserve one durable commit
    Given one authenticated request identity, nonce, nullifier, and expected head
    When "<retry_case>" occurs through independent mounted clients
    Then the durable classifier matches "fcis_m6_nonce_retry_classifier_v1"
    And at most one semantic commit and nullifier exist
    And INDETERMINATE is only a client observation resolved by fresh lookup

    Examples:
      | retry_case |
      | first_commit |
      | exact_concurrent_retry |
      | same_id_different_fingerprint |
      | nullifier_conflict |
      | stale_expected_head |
      | response_lost_after_commit |
      | request_lost_before_server |

  @model_fcis_m6_history_fixed_point_v1
  Scenario Outline: Only complete canonical history fixed points reopen
    Given a canonical committed layout exists
    When "<history_fault>" is applied and every attacker-controlled cache is recomputed
    Then canonical reopen either reconstructs the exact complete authorized history or rejects and locks
    And an accepted layout equals the canonical re-encoding of the reconstructed history

    Examples:
      | history_fault |
      | missing_state_row |
      | missing_history_row |
      | missing_evidence_row |
      | missing_nullifier_row |
      | missing_receipt_row |
      | missing_outbox_row |
      | missing_authority_row |
      | crossed_relation |
      | surplus_row |
      | reordered_layout |

  @model_fcis_m6_proof_context_v1
  Scenario Outline: Proof authority cannot be substituted by caller data
    Given the mounted verifier registry is pinned by the promotion subject
    When a proof has "<context_fault>"
    Then the proof decision matches "fcis_m6_proof_context_v1"
    And no caller-supplied verifier, key, schema, algorithm, state root, deployment, or public-input root is accepted

    Examples:
      | context_fault |
      | NONE |
      | DEPLOYMENT |
      | STATE |
      | CONFIG |
      | VERIFIER |
      | KEY |
      | SCHEMA |
      | ALGORITHM |
      | FRESHNESS |
      | CALLER_PUBLIC_INPUT |

  @model_fcis_m6_oracle_risk_gate_v1
  Scenario Outline: Risk-increasing value movement requires exact finalized oracle authority
    Given a price-dependent command is classified as "<risk_class>"
    And the oracle context is "<oracle_status>"
    When the command is evaluated through the mounted authority runtime
    Then the decision matches "fcis_m6_oracle_risk_gate_v1"
    And every accepted value change carries the exact economic certificate
    And pending, stale, nonpositive, unseen, unbound, or deficit contexts cannot authorize risk increase

    Examples:
      | risk_class | oracle_status |
      | risk_increase | FINAL_FRESH |
      | risk_increase | PENDING |
      | risk_increase | STALE |
      | risk_increase | FINAL_DEFICIT |
      | risk_reduce | FINAL_FRESH |
      | risk_reduce | FINAL_DEFICIT |
