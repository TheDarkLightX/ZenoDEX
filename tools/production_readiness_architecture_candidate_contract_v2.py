"""Checker-owned contract for the detailed V2 architecture candidate.

The JSON manifest is untrusted input.  This module owns the closed command,
module, state, type, port, route, ordering, and evidence registries against
which that input is checked.
"""

from __future__ import annotations

from typing import Any, Final

SCHEMA: Final = "zenodex/production-readiness-architecture-candidate/v2"
CHECK_SCHEMA: Final = "zenodex/production-readiness-architecture-candidate-check/v2"
REVIEWED_SUBJECT: Final = "64b20a6a6800eb03fc6a9cf986c82e826c80ced6"
PARENT_CANDIDATE_ID: Final = "TYPED_SETTLEMENT_MICROKERNEL_V2"

EXPECTED_SOURCE_PATHS: Final = (
    "docs/PRODUCTION_READINESS_PLAN.md",
    "docs/research/PRODUCTION_READINESS_ARCHITECTURE_CANDIDATE_V2.md",
    "docs/research/PRODUCTION_READINESS_ARCHITECTURE_TOURNAMENT_V1.json",
    "docs/research/PRODUCTION_READINESS_G1_SEMANTICS_V1.json",
    "docs/research/PRODUCTION_READINESS_TASK_GRAPH_V1.json",
    "tools/check_production_readiness_architecture_tournament_v1.py",
    "tools/production_readiness_architecture_candidate_contract_v2.py",
    "tools/render_production_readiness_architecture_candidate_v2.py",
)

EXPECTED_VERIFIER_BOOTSTRAP: Final = {
    "checker_path": "tools/check_production_readiness_architecture_candidate_v2.py",
    "identity_status": "REQUIRED_EXTERNAL_AUTHENTICATED_RECEIPT",
    "external_receipt_required": True,
    "self_verification_allowed": False,
    "promotion_use_allowed": False,
}

EXPECTED_MODULE_COMMANDS: Final[dict[str, tuple[str, ...]]] = {
    "SPOT_LP_MODULE": ("lp_add", "lp_remove", "spot_swap"),
    "ORACLE_MODULE": ("oracle_dispute", "oracle_submit"),
    "ZUSD_MODULE": (
        "stability_pool_deposit",
        "stability_pool_withdraw",
        "zusd_borrow",
        "zusd_liquidate",
        "zusd_redeem",
        "zusd_redistribute",
        "zusd_repay",
    ),
    "PERPS_MODULE": ("perp_close", "perp_funding", "perp_liquidate", "perp_open"),
    "SELLER_AUCTION_MODULE": (
        "seller_auction_cancel",
        "seller_auction_commit",
        "seller_auction_expire",
        "seller_auction_reveal",
        "seller_auction_settle",
    ),
    "PRIVATE_SWAP_MODULE": (
        "private_swap_cancel",
        "private_swap_commit",
        "private_swap_expire",
        "private_swap_reveal",
        "private_swap_settle",
    ),
    "TAU_ESCROW_MODULE": (
        "fallback_activate",
        "tau_escrow_deposit",
        "tau_rejoin",
        "tau_withdrawal",
        "tau_withdrawal_ack",
    ),
    "PROOF_REWARD_MODULE": ("zrpf_prover_reward",),
    "PROTOCOL_FINANCE_MODULE": ("protocol_buy_and_burn",),
}
EXPECTED_COMMANDS: Final = frozenset(
    command_id for command_ids in EXPECTED_MODULE_COMMANDS.values() for command_id in command_ids
)

INFRASTRUCTURE_MODULES: Final = frozenset(
    {
        "COMMAND_ROUTER",
        "GOVERNANCE_VERIFIER_ADAPTER",
        "OUTBOX_SHELL",
        "POLICY_KERNEL",
        "POLICY_VERIFIER_ADAPTER",
        "RELEASE_KERNEL",
        "RISC0_GUEST",
        "RISC0_VERIFIER_ADAPTER",
        "SETTLEMENT_ABI",
        "SETTLEMENT_KERNEL",
        "ZENO_LEDGER",
    }
)
EXPECTED_MODULES: Final = frozenset(EXPECTED_MODULE_COMMANDS) | INFRASTRUCTURE_MODULES

EXPECTED_STATE_OWNERS: Final[dict[str, str]] = {
    "ECONOMIC_LEDGER": "SETTLEMENT_KERNEL",
    "REPLAY_HISTORY_OUTBOX": "SETTLEMENT_KERNEL",
    "RELEASE_SELECTION_MIGRATION": "RELEASE_KERNEL",
    "POLICY_PROFILE_REGISTRY": "POLICY_KERNEL",
    "SPOT_LP_STATE": "SPOT_LP_MODULE",
    "ORACLE_STATE": "ORACLE_MODULE",
    "ZUSD_STATE": "ZUSD_MODULE",
    "PERPS_STATE": "PERPS_MODULE",
    "SELLER_AUCTION_STATE": "SELLER_AUCTION_MODULE",
    "PRIVATE_SWAP_STATE": "PRIVATE_SWAP_MODULE",
    "TAU_ESCROW_STATE": "TAU_ESCROW_MODULE",
    "PROOF_REWARD_STATE": "PROOF_REWARD_MODULE",
    "PROTOCOL_FINANCE_STATE": "PROTOCOL_FINANCE_MODULE",
}

EXPECTED_INTENTS: Final = frozenset(
    {
        "AUTHORIZED_BURN",
        "AUTHORIZED_ISSUE",
        "CUSTODY_CHANGE",
        "ESCROW_CHANGE",
        "LEDGER_TRANSFER",
        "LIABILITY_CHANGE",
        "NULLIFIER_CONSUME",
        "ORACLE_OCCURRENCE_RECORD",
        "OUTBOX_ENQUEUE",
        "MODULE_RELEASE_LIFECYCLE_CHANGE",
        "POLICY_PROFILE_CHANGE",
        "RESERVE_CHANGE",
        "TAU_CONNECTIVITY_MODE_CHANGE",
        "TERMINAL_OBLIGATION_CHANGE",
    }
)

EXPECTED_VIEW_IDS: Final = frozenset(
    {
        "AUTHENTICATED_ORACLE_VIEW",
        "ECONOMIC_VIEW",
        "RESOLVED_RELEASE_VIEW",
        "RESOLVED_TAU_REPRESENTATION",
        "VERIFIED_POLICY_ADMISSION",
    }
)

EXPECTED_ROUTE_CONSTRAINT_IDS: Final = frozenset(
    {
        "AT_LEAST_TWO_LEDGER_TRANSFER_LEGS",
        "EXACTLY_ONE_TAU_DEPOSIT_REPRESENTATION_LANE",
        "EXACTLY_ONE_TAU_WITHDRAWAL_REPRESENTATION_LANE",
        "NO_DUPLICATE_SOURCE_LOT",
        "SURPLUS_PRIORITY_AND_BURN_FLOOR",
    }
)

def _field(
    field_id: str,
    value_type: str,
    *,
    unit: str = "NONE",
    cardinality: str = "ONE",
) -> dict[str, str]:
    return {
        "id": field_id,
        "value_type": value_type,
        "unit": unit,
        "cardinality": cardinality,
    }


def _type_spec(
    type_id: str,
    fields: tuple[dict[str, str], ...],
    *,
    variants: tuple[str, ...] = (),
    variant_discriminator: str | None = None,
    variant_field_contracts: dict[str, dict[str, tuple[str, ...]]] | None = None,
    nested_schema_status: str = "EXACT_FIELD_NAMES_TYPES_UNITS_V2",
) -> dict[str, Any]:
    contracts = variant_field_contracts or {}
    return {
        "id": type_id,
        "canonical_codec": "ZENODEX_CANONICAL_CODEC_V2",
        "closed_fields": True,
        "caller_constructible_authority": False,
        "field_specs": list(fields),
        "variant_ids": list(variants),
        "variant_discriminator": variant_discriminator,
        "variant_field_contracts": {
            variant_id: {
                "required_field_ids": list(contract["required"]),
                "forbidden_field_ids": list(contract["forbidden"]),
            }
            for variant_id, contract in contracts.items()
        },
        "nested_schema_status": nested_schema_status,
    }


_ROOT = "HASH32"
_ID = "CANONICAL_ID"
_U64 = "U64_CHECKED"
_U32 = "U32_CHECKED"
_U16 = "U16_CHECKED"
_ATOMS = "U256_CHECKED"

EXPECTED_TYPE_SPECS: Final[dict[str, dict[str, Any]]] = {
    "AcceptCandidateV2": _type_spec(
        "AcceptCandidateV2",
        (
            _field("execution_admission", "ExecutionAdmissionV2"),
            _field("candidate_root", _ROOT),
            _field("commit_capability_id", _ID),
        ),
    ),
    "AuthorizedPolicyControlRequestV2": _type_spec(
        "AuthorizedPolicyControlRequestV2",
        (
            _field("control_root", _ROOT),
            _field("policy_change", "PolicyProfileControlV2"),
            _field("authorization", "VerifiedGovernanceAuthorizationV2"),
        ),
    ),
    "AuthorizedReleaseControlRequestV2": _type_spec(
        "AuthorizedReleaseControlRequestV2",
        (
            _field("control_root", _ROOT),
            _field("release_change", "ModuleReleaseControlV2"),
            _field("authorization", "VerifiedGovernanceAuthorizationV2"),
        ),
    ),
    "AuthenticatedExecutionContextV2": _type_spec(
        "AuthenticatedExecutionContextV2",
        (
            _field("parent_state_root", _ROOT),
            _field("height", _U64, unit="LEDGER_HEIGHT"),
            _field("sender", _ID),
            _field("nonce", _U64, unit="NONCE"),
            _field("epoch", _U64, unit="EPOCH"),
            _field("oracle_context_root", _ROOT),
            _field("deployment_root", _ROOT),
            _field("tau_evidence_root", _ROOT, cardinality="ZERO_OR_ONE"),
        ),
    ),
    "AuthenticatedExecutionRequestV2": _type_spec(
        "AuthenticatedExecutionRequestV2",
        (
            _field("promotion_subject_root", _ROOT),
            _field("writer_epoch", _U64, unit="EPOCH"),
            _field("command_index", _U32, unit="BATCH_INDEX"),
            _field("command", "GlobalCommandV2"),
            _field("context", "AuthenticatedExecutionContextV2"),
            _field("pre_state", "GlobalEconomicStateV2"),
        ),
    ),
    "AuthenticatedOracleViewV2": _type_spec(
        "AuthenticatedOracleViewV2",
        (
            _field("source_state_root", _ROOT),
            _field("profile_root", _ROOT),
            _field("occurrence_root", _ROOT),
            _field("oracle_point_set_root", _ROOT),
            _field("as_of_height", _U64, unit="LEDGER_HEIGHT"),
            _field("freshness_limit_blocks", _U64, unit="BLOCK_COUNT"),
            _field("dispute_state_root", _ROOT),
        ),
    ),
    "CommittedOutboxEnvelopeV2": _type_spec(
        "CommittedOutboxEnvelopeV2",
        (
            _field("destination_id", _ID),
            _field("outbox_id", _ID),
            _field("payload_root", _ROOT),
            _field("promotion_subject_root", _ROOT),
            _field("publication_root", _ROOT),
            _field("writer_epoch", _U64, unit="EPOCH"),
        ),
    ),
    "FinalityCertificateV2": _type_spec(
        "FinalityCertificateV2",
        (
            _field("validator_registry_root", _ROOT),
            _field("block_root", _ROOT),
            _field("height", _U64, unit="LEDGER_HEIGHT"),
            _field("round", _U32, unit="CONSENSUS_ROUND"),
            _field("precommit_set_root", _ROOT),
        ),
    ),
    "EconomicViewV2": _type_spec(
        "EconomicViewV2",
        (
            _field("source_state_root", _ROOT),
            _field("occurrence_root", _ROOT),
            _field("module_id", _ID),
            _field("authorized_projection_root", _ROOT),
            _field("projection_schema_root", _ROOT),
        ),
        nested_schema_status="PER_MODULE_READ_PROJECTIONS_REQUIRED_NOT_IMPLEMENTED_G2",
    ),
    "ExecutionCommitmentsV2": _type_spec(
        "ExecutionCommitmentsV2",
        (
            _field("promotion_subject_root", _ROOT),
            _field("parent_state_root", _ROOT),
            _field("writer_epoch", _U64, unit="EPOCH"),
            _field("pre_state_root", _ROOT),
            _field("post_state_root", _ROOT),
            _field("value_delta_root", _ROOT),
            _field("effect_plan_root", _ROOT),
            _field("history_root", _ROOT),
            _field("nullifier_root", _ROOT),
            _field("outbox_root", _ROOT),
            _field("module_release_set_root", _ROOT),
            _field("policy_profile_root", _ROOT),
        ),
    ),
    "ExecutionAdmissionV2": _type_spec(
        "ExecutionAdmissionV2",
        (
            _field("mode", _ID),
            _field("opaque_admission_id", _ID),
            _field("commitments", "ExecutionCommitmentsV2"),
            _field("value_delta", "ValueDeltaCertificateV2"),
            _field("proof_record", "ProofRecordV2"),
            _field(
                "verified_zrpf_journal",
                "VerifiedZRPFJournalV2",
                cardinality="ZERO_OR_ONE",
            ),
        ),
        variants=("DIRECT_EXECUTION", "ZRPF_ROOT"),
        variant_discriminator="mode",
        variant_field_contracts={
            "DIRECT_EXECUTION": {
                "required": (
                    "mode",
                    "opaque_admission_id",
                    "commitments",
                    "value_delta",
                    "proof_record",
                ),
                "forbidden": ("verified_zrpf_journal",),
            },
            "ZRPF_ROOT": {
                "required": (
                    "mode",
                    "opaque_admission_id",
                    "commitments",
                    "value_delta",
                    "proof_record",
                    "verified_zrpf_journal",
                ),
                "forbidden": (),
            },
        },
    ),
    "GlobalCommandV2": _type_spec(
        "GlobalCommandV2",
        (
            _field("command_id", _ID),
            _field("payload_schema_root", _ROOT),
            _field("payload_root", _ROOT),
            _field("payload_bytes", "BOUNDED_BYTES"),
        ),
        variants=tuple(sorted(EXPECTED_COMMANDS)),
        variant_discriminator="command_id",
        variant_field_contracts={
            command_id: {
                "required": (
                    "command_id",
                    "payload_schema_root",
                    "payload_root",
                    "payload_bytes",
                ),
                "forbidden": (),
            }
            for command_id in sorted(EXPECTED_COMMANDS)
        },
        nested_schema_status="COMMAND_VARIANT_FIELDS_REQUIRED_NOT_SELECTED_G1",
    ),
    "GlobalEconomicStateV2": _type_spec(
        "GlobalEconomicStateV2",
        tuple(
            _field(field_id, _ROOT)
            for field_id in (
                "balances_root",
                "custody_root",
                "supply_root",
                "debt_root",
                "lp_state_root",
                "perps_liabilities_root",
                "escrows_root",
                "reserves_root",
                "auctions_root",
                "withdrawals_root",
                "outbox_root",
                "history_root",
                "nullifiers_root",
                "release_state_root",
                "policy_profile_root",
            )
        ),
        nested_schema_status="DOMAIN_OBJECT_SCHEMAS_REQUIRED_NOT_IMPLEMENTED_G1_G2",
    ),
    "GlobalOutcomeV2": _type_spec(
        "GlobalOutcomeV2",
        (
            _field("variant", _ID),
            _field("reject", "RejectNoCommitV2", cardinality="ZERO_OR_ONE"),
            _field("accept", "AcceptCandidateV2", cardinality="ZERO_OR_ONE"),
        ),
        variants=("REJECT_NO_COMMIT", "ACCEPT_CANDIDATE"),
        variant_discriminator="variant",
        variant_field_contracts={
            "REJECT_NO_COMMIT": {
                "required": ("variant", "reject"),
                "forbidden": ("accept",),
            },
            "ACCEPT_CANDIDATE": {
                "required": ("variant", "accept"),
                "forbidden": ("reject",),
            },
        },
    ),
    "GovernedEpochControlV2": _type_spec(
        "GovernedEpochControlV2",
        (
            _field("variant", _ID),
            _field("promotion_subject_root", _ROOT),
            _field("expected_parent_root", _ROOT),
            _field("writer_epoch", _U64, unit="EPOCH"),
            _field("control_nonce", _U64, unit="NONCE"),
            _field("effective_epoch", _U64, unit="EPOCH"),
            _field("governance_witness_root", _ROOT),
            _field("release_change", "ModuleReleaseControlV2", cardinality="ZERO_OR_ONE"),
            _field("policy_change", "PolicyProfileControlV2", cardinality="ZERO_OR_ONE"),
        ),
        variants=(
            "MODULE_RELEASE_ONLY",
            "POLICY_PROFILE_ONLY",
            "ATOMIC_RELEASE_AND_POLICY",
        ),
        variant_discriminator="variant",
        variant_field_contracts={
            "MODULE_RELEASE_ONLY": {
                "required": (
                    "variant",
                    "promotion_subject_root",
                    "expected_parent_root",
                    "writer_epoch",
                    "control_nonce",
                    "effective_epoch",
                    "governance_witness_root",
                    "release_change",
                ),
                "forbidden": ("policy_change",),
            },
            "POLICY_PROFILE_ONLY": {
                "required": (
                    "variant",
                    "promotion_subject_root",
                    "expected_parent_root",
                    "writer_epoch",
                    "control_nonce",
                    "effective_epoch",
                    "governance_witness_root",
                    "policy_change",
                ),
                "forbidden": ("release_change",),
            },
            "ATOMIC_RELEASE_AND_POLICY": {
                "required": (
                    "variant",
                    "promotion_subject_root",
                    "expected_parent_root",
                    "writer_epoch",
                    "control_nonce",
                    "effective_epoch",
                    "governance_witness_root",
                    "release_change",
                    "policy_change",
                ),
                "forbidden": (),
            },
        },
    ),
    "GovernedEpochControlOutcomeV2": _type_spec(
        "GovernedEpochControlOutcomeV2",
        (
            _field("variant", _ID),
            _field("reject", "RejectNoCommitV2", cardinality="ZERO_OR_ONE"),
            _field("publication", "PublicationBundleV2", cardinality="ZERO_OR_ONE"),
        ),
        variants=("REJECT_NO_COMMIT", "ACCEPT_PUBLISHED"),
        variant_discriminator="variant",
        variant_field_contracts={
            "REJECT_NO_COMMIT": {
                "required": ("variant", "reject"),
                "forbidden": ("publication",),
            },
            "ACCEPT_PUBLISHED": {
                "required": ("variant", "publication"),
                "forbidden": ("reject",),
            },
        },
    ),
    "GovernanceAuthorizationQueryV2": _type_spec(
        "GovernanceAuthorizationQueryV2",
        (
            _field("control_root", _ROOT),
            _field("promotion_subject_root", _ROOT),
            _field("expected_parent_root", _ROOT),
            _field("writer_epoch", _U64, unit="EPOCH"),
            _field("governance_registry_root", _ROOT),
            _field("governance_witness_root", _ROOT),
        ),
    ),
    "KernelIntentV2": _type_spec(
        "KernelIntentV2",
        (
            _field("intent_id", _ID),
            _field("module_id", _ID),
            _field("route_step_index", _U16, unit="ROUTE_STEP_INDEX"),
            _field("intent_index", _U16, unit="INTENT_INDEX"),
            _field("authority_profile_id", _ID),
            _field("source_lot_roots", _ROOT, cardinality="ZERO_OR_MORE_CANONICAL"),
            _field("variant_payload_root", _ROOT),
        ),
        variants=tuple(sorted(EXPECTED_INTENTS)),
        variant_discriminator="intent_id",
        variant_field_contracts={
            intent_id: {
                "required": (
                    "intent_id",
                    "module_id",
                    "route_step_index",
                    "intent_index",
                    "authority_profile_id",
                    "source_lot_roots",
                    "variant_payload_root",
                ),
                "forbidden": (),
            }
            for intent_id in sorted(EXPECTED_INTENTS)
        },
    ),
    "ModuleExecutionRequestV2": _type_spec(
        "ModuleExecutionRequestV2",
        (
            _field("occurrence_root", _ROOT),
            _field("module_release_set_root", _ROOT),
            _field("route_step_index", _U16, unit="ROUTE_STEP_INDEX"),
            _field("pre_state_root", _ROOT),
            _field("required_views_root", _ROOT),
            _field("verified_admission", "VerifiedAdmissionV2"),
            _field("command", "GlobalCommandV2"),
        ),
    ),
    "ModuleOutcomeV2": _type_spec(
        "ModuleOutcomeV2",
        (
            _field("variant", _ID),
            _field("reject_code", _ID, cardinality="ZERO_OR_ONE"),
            _field("ordered_intents", "KernelIntentV2", cardinality="ZERO_OR_MORE_CANONICAL"),
            _field("local_post_state_root", _ROOT, cardinality="ZERO_OR_ONE"),
        ),
        variants=("REJECT", "PROPOSE_INTENTS"),
        variant_discriminator="variant",
        variant_field_contracts={
            "REJECT": {
                "required": ("variant", "reject_code"),
                "forbidden": ("ordered_intents", "local_post_state_root"),
            },
            "PROPOSE_INTENTS": {
                "required": ("variant", "ordered_intents", "local_post_state_root"),
                "forbidden": ("reject_code",),
            },
        },
    ),
    "ModuleReleaseControlV2": _type_spec(
        "ModuleReleaseControlV2",
        (
            _field("module_id", _ID),
            _field("from_release_id", _ID),
            _field("to_release_id", _ID),
            _field("lifecycle_transition", _ID),
            _field("migration_inventory_root", _ROOT),
        ),
    ),
    "OracleViewQueryV2": _type_spec(
        "OracleViewQueryV2",
        (
            _field("parent_state_root", _ROOT),
            _field("profile_root", _ROOT),
            _field("context_root", _ROOT),
            _field("occurrence_root", _ROOT),
            _field("requested_feed_ids_root", _ROOT),
        ),
    ),
    "OutboxAckCommandV2": _type_spec(
        "OutboxAckCommandV2",
        (
            _field("command_id", _ID),
            _field("destination_id", _ID),
            _field("outbox_id", _ID),
            _field("payload_root", _ROOT),
            _field("promotion_subject_root", _ROOT),
            _field("publication_root", _ROOT),
            _field("writer_epoch", _U64, unit="EPOCH"),
            _field("delivery_receipt_root", _ROOT),
        ),
    ),
    "OutboxDeliveryReceiptV2": _type_spec(
        "OutboxDeliveryReceiptV2",
        (
            _field("destination_id", _ID),
            _field("outbox_id", _ID),
            _field("payload_root", _ROOT),
            _field("publication_root", _ROOT),
            _field("destination_receipt_root", _ROOT),
            _field("delivery_result", _ID),
        ),
    ),
    "PolicyBackendQueryV2": _type_spec(
        "PolicyBackendQueryV2",
        (
            _field("query_root", _ROOT),
            _field("backend_id", _ID),
            _field("implementation_root", _ROOT),
            _field("toolchain_root", _ROOT),
            _field("profile_root", _ROOT),
            _field("verifier_registry_root", _ROOT),
            _field("verifier_execution_profile_root", _ROOT),
            _field("active_policy_epoch", _U64, unit="EPOCH"),
        ),
    ),
    "PolicyBackendReceiptV2": _type_spec(
        "PolicyBackendReceiptV2",
        (
            _field("query_root", _ROOT),
            _field("backend_id", _ID),
            _field("result", _ID),
            _field("result_root", _ROOT),
            _field("signature_or_replay_output_root", _ROOT),
            _field("verifier_registry_root", _ROOT),
            _field("verifier_execution_profile_root", _ROOT),
            _field("active_policy_epoch", _U64, unit="EPOCH"),
        ),
    ),
    "PolicyProfileControlV2": _type_spec(
        "PolicyProfileControlV2",
        (
            _field("from_profile_root", _ROOT),
            _field("to_profile_root", _ROOT),
            _field("activation_epoch", _U64, unit="EPOCH"),
            _field("compatibility_proof_root", _ROOT),
            _field("from_verifier_execution_profile_root", _ROOT),
            _field("to_verifier_execution_profile", "VerifierExecutionProfileV2"),
            _field("equivalence_receipt_root", _ROOT, cardinality="ZERO_OR_ONE"),
        ),
    ),
    "PolicyQueryV2": _type_spec(
        "PolicyQueryV2",
        (
            _field("occurrence_root", _ROOT),
            _field("profile_root", _ROOT),
            _field("module_release_set_root", _ROOT),
            _field("verifier_registry_root", _ROOT),
            _field("policy_claim_root", _ROOT),
            _field("verifier_execution_profile", "VerifierExecutionProfileV2"),
            _field("active_policy_epoch", _U64, unit="EPOCH"),
        ),
    ),
    "ProofRecordV2": _type_spec(
        "ProofRecordV2",
        (
            _field("proof_mode", _ID),
            _field("proof_root", _ROOT),
            _field("image_id", _ID, cardinality="ZERO_OR_ONE"),
            _field("journal_root", _ROOT, cardinality="ZERO_OR_ONE"),
            _field("verifier_profile_root", _ROOT),
            _field("verifier_registry_root", _ROOT),
            _field("verified_witness_id", _ID, cardinality="ZERO_OR_ONE"),
        ),
        variants=("DIRECT_EXECUTION", "ZRPF_ROOT"),
        variant_discriminator="proof_mode",
        variant_field_contracts={
            "DIRECT_EXECUTION": {
                "required": (
                    "proof_mode",
                    "proof_root",
                    "verifier_profile_root",
                    "verifier_registry_root",
                ),
                "forbidden": ("image_id", "journal_root", "verified_witness_id"),
            },
            "ZRPF_ROOT": {
                "required": (
                    "proof_mode",
                    "proof_root",
                    "image_id",
                    "journal_root",
                    "verifier_profile_root",
                    "verifier_registry_root",
                    "verified_witness_id",
                ),
                "forbidden": (),
            },
        },
    ),
    "PublicationBundleV2": _type_spec(
        "PublicationBundleV2",
        (
            _field("candidate", "AcceptCandidateV2"),
            _field("finality_certificate", "FinalityCertificateV2"),
            _field("publication_root", _ROOT),
            _field("successor_head_root", _ROOT),
        ),
    ),
    "RejectNoCommitV2": _type_spec(
        "RejectNoCommitV2",
        (
            _field("reject_code", _ID),
            _field("pre_state_root", _ROOT),
            _field("post_state_root", _ROOT),
            _field("effect_count", _U32, unit="COUNT"),
        ),
    ),
    "ReleaseQueryV2": _type_spec(
        "ReleaseQueryV2",
        (
            _field("promotion_subject_root", _ROOT),
            _field("profile_root", _ROOT),
            _field("route_id", _ID),
            _field("creator_release_ids_root", _ROOT),
            _field("epoch", _U64, unit="EPOCH"),
        ),
    ),
    "ResolvedReleaseSetV2": _type_spec(
        "ResolvedReleaseSetV2",
        (
            _field("module_release_entries_root", _ROOT),
            _field("module_release_set_root", _ROOT),
            _field("profile_root", _ROOT),
            _field("release_registry_root", _ROOT),
        ),
    ),
    "ResolvedRouteV2": _type_spec(
        "ResolvedRouteV2",
        (
            _field("route_id", _ID),
            _field("ordered_step_root", _ROOT),
            _field("required_view_ids_root", _ROOT),
            _field("required_intent_ids_root", _ROOT),
            _field("constraint_ids_root", _ROOT),
            _field("source_registry_root", _ROOT),
        ),
    ),
    "RouteQueryV2": _type_spec(
        "RouteQueryV2",
        (
            _field("command_id", _ID),
            _field("command_schema_root", _ROOT),
            _field("promotion_subject_root", _ROOT),
            _field("route_registry_root", _ROOT),
        ),
    ),
    "ResolvedTauRepresentationV2": _type_spec(
        "ResolvedTauRepresentationV2",
        (
            _field("asset_id", _ID),
            _field("external_asset_id", _ID),
            _field("representation_lane", _ID),
            _field("issue_authority_profile_id", _ID, cardinality="ZERO_OR_ONE"),
            _field("burn_authority_profile_id", _ID, cardinality="ZERO_OR_ONE"),
            _field("custody_account_role", _ID),
            _field("asset_decimals", _U16, unit="DECIMAL_PLACES"),
            _field("scale_numerator", _ATOMS, unit="RATIONAL_NUMERATOR"),
            _field("scale_denominator", _ATOMS, unit="RATIONAL_DENOMINATOR"),
            _field("rounding_mode", _ID),
            _field("dust_policy_id", _ID),
            _field("external_network_profile_root", _ROOT),
            _field("ingress_verifier_profile_root", _ROOT),
            _field("destination_adapter_root", _ROOT),
            _field("migration_policy_root", _ROOT),
            _field("recovery_policy_root", _ROOT),
            _field("permanence_anchor_root", _ROOT),
            _field("policy_profile_root", _ROOT),
            _field("module_release_set_root", _ROOT),
        ),
        variants=("TRANSFER_LOCK", "MINT_BURN"),
        variant_discriminator="representation_lane",
        variant_field_contracts={
            "TRANSFER_LOCK": {
                "required": (
                    "asset_id",
                    "external_asset_id",
                    "representation_lane",
                    "custody_account_role",
                    "asset_decimals",
                    "scale_numerator",
                    "scale_denominator",
                    "rounding_mode",
                    "dust_policy_id",
                    "external_network_profile_root",
                    "ingress_verifier_profile_root",
                    "destination_adapter_root",
                    "migration_policy_root",
                    "recovery_policy_root",
                    "permanence_anchor_root",
                    "policy_profile_root",
                    "module_release_set_root",
                ),
                "forbidden": (
                    "issue_authority_profile_id",
                    "burn_authority_profile_id",
                ),
            },
            "MINT_BURN": {
                "required": (
                    "asset_id",
                    "external_asset_id",
                    "representation_lane",
                    "issue_authority_profile_id",
                    "burn_authority_profile_id",
                    "custody_account_role",
                    "asset_decimals",
                    "scale_numerator",
                    "scale_denominator",
                    "rounding_mode",
                    "dust_policy_id",
                    "external_network_profile_root",
                    "ingress_verifier_profile_root",
                    "destination_adapter_root",
                    "migration_policy_root",
                    "recovery_policy_root",
                    "permanence_anchor_root",
                    "policy_profile_root",
                    "module_release_set_root",
                ),
                "forbidden": (),
            },
        },
    ),
    "SubmissionReceiptV2": _type_spec(
        "SubmissionReceiptV2",
        (
            _field("submission_id", _ID),
            _field("command_root", _ROOT),
            _field("accepted_for_ordering", "BOOL"),
            _field("writer_epoch", _U64, unit="EPOCH"),
        ),
    ),
    "TauRepresentationQueryV2": _type_spec(
        "TauRepresentationQueryV2",
        (
            _field("command_id", _ID),
            _field("asset_id", _ID),
            _field("policy_profile_root", _ROOT),
            _field("module_release_set_root", _ROOT),
            _field("promotion_subject_root", _ROOT),
        ),
    ),
    "ValueDeltaCertificateV2": _type_spec(
        "ValueDeltaCertificateV2",
        tuple(
            _field(field_id, _ROOT)
            for field_id in (
                "balance_delta_root",
                "custody_delta_root",
                "supply_delta_root",
                "debt_delta_root",
                "lp_delta_root",
                "perps_delta_root",
                "escrow_delta_root",
                "reserve_delta_root",
                "auction_delta_root",
                "withdrawal_delta_root",
                "outbox_delta_root",
                "history_delta_root",
                "nullifier_delta_root",
                "release_delta_root",
                "policy_delta_root",
            )
        ),
        nested_schema_status="DELTA_ENTRY_SCHEMAS_REQUIRED_NOT_IMPLEMENTED_G1_G2",
    ),
    "VerifierExecutionProfileV2": _type_spec(
        "VerifierExecutionProfileV2",
        (
            _field("profile_id", _ID),
            _field("normal_backend_set_root", _ROOT),
            _field("outage_backend_set_root", _ROOT, cardinality="ZERO_OR_ONE"),
            _field("active_mode", _ID),
            _field("activation_epoch", _U64, unit="EPOCH"),
            _field("equivalence_receipt_root", _ROOT, cardinality="ZERO_OR_ONE"),
            _field("governance_authorization_root", _ROOT, cardinality="ZERO_OR_ONE"),
            _field("fallback_policy_id", _ID),
        ),
        variants=("NATIVE_ONLY", "NATIVE_AND_TAU", "TAU_PRIMARY", "NATIVE_BACKUP"),
        variant_discriminator="active_mode",
        variant_field_contracts={
            "NATIVE_ONLY": {
                "required": (
                    "profile_id",
                    "normal_backend_set_root",
                    "active_mode",
                    "activation_epoch",
                    "fallback_policy_id",
                ),
                "forbidden": (
                    "outage_backend_set_root",
                    "equivalence_receipt_root",
                    "governance_authorization_root",
                ),
            },
            "NATIVE_AND_TAU": {
                "required": (
                    "profile_id",
                    "normal_backend_set_root",
                    "active_mode",
                    "activation_epoch",
                    "equivalence_receipt_root",
                    "governance_authorization_root",
                    "fallback_policy_id",
                ),
                "forbidden": ("outage_backend_set_root",),
            },
            "TAU_PRIMARY": {
                "required": (
                    "profile_id",
                    "normal_backend_set_root",
                    "outage_backend_set_root",
                    "active_mode",
                    "activation_epoch",
                    "equivalence_receipt_root",
                    "governance_authorization_root",
                    "fallback_policy_id",
                ),
                "forbidden": (),
            },
            "NATIVE_BACKUP": {
                "required": (
                    "profile_id",
                    "normal_backend_set_root",
                    "outage_backend_set_root",
                    "active_mode",
                    "activation_epoch",
                    "equivalence_receipt_root",
                    "governance_authorization_root",
                    "fallback_policy_id",
                ),
                "forbidden": (),
            },
        },
    ),
    "VerifiedAdmissionV2": _type_spec(
        "VerifiedAdmissionV2",
        (
            _field("opaque_witness_id", _ID),
            _field("query_root", _ROOT),
            _field("profile_root", _ROOT),
            _field("module_release_set_root", _ROOT),
            _field("verifier_registry_root", _ROOT),
            _field("backend_receipt_set_root", _ROOT),
            _field("verifier_execution_profile_root", _ROOT),
            _field("active_policy_epoch", _U64, unit="EPOCH"),
            _field("active_backend_set_root", _ROOT),
            _field("equivalence_receipt_root", _ROOT, cardinality="ZERO_OR_ONE"),
        ),
    ),
    "VerifiedGovernanceAuthorizationV2": _type_spec(
        "VerifiedGovernanceAuthorizationV2",
        (
            _field("opaque_witness_id", _ID),
            _field("control_root", _ROOT),
            _field("governance_registry_root", _ROOT),
            _field("promotion_subject_root", _ROOT),
            _field("expected_parent_root", _ROOT),
            _field("writer_epoch", _U64, unit="EPOCH"),
        ),
    ),
    "VerifiedZRPFWitnessV2": _type_spec(
        "VerifiedZRPFWitnessV2",
        (
            _field("opaque_witness_id", _ID),
            _field("proof_root", _ROOT),
            _field("journal_root", _ROOT),
            _field("image_id", _ID),
            _field("verifier_profile_root", _ROOT),
            _field("verifier_registry_root", _ROOT),
            _field("promotion_subject_root", _ROOT),
        ),
    ),
    "VerifiedZRPFJournalV2": _type_spec(
        "VerifiedZRPFJournalV2",
        (
            _field("witness", "VerifiedZRPFWitnessV2"),
            _field("journal", "ZRPFRootJournalV2"),
            _field("exact_journal_bytes_root", _ROOT),
        ),
    ),
    "ZRPFProofQueryV2": _type_spec(
        "ZRPFProofQueryV2",
        (
            _field("promotion_subject_root", _ROOT),
            _field("expected_parent_root", _ROOT),
            _field("writer_epoch", _U64, unit="EPOCH"),
            _field("proof_root", _ROOT),
            _field("image_id", _ID),
            _field("journal_bytes", "BOUNDED_BYTES"),
            _field("journal_root", _ROOT),
            _field("verifier_profile_root", _ROOT),
            _field("verifier_registry_root", _ROOT),
        ),
    ),
    "ZRPFRootJournalV2": _type_spec(
        "ZRPFRootJournalV2",
        (
            _field("ordered_command_root", _ROOT),
            _field("context_root", _ROOT),
            _field("commitments", "ExecutionCommitmentsV2"),
            _field("verifier_profile_root", _ROOT),
            _field("command_count", _U16, unit="COUNT"),
        ),
    ),
}

EXPECTED_COMMAND_PAYLOAD_SCHEMAS: Final[dict[str, dict[str, Any]]] = {
    command_id: {
        "command_id": command_id,
        "source_semantics_id": command_id,
        "schema_status": "REQUIRED_NOT_SELECTED_G1",
        "field_specs": [],
    }
    for command_id in EXPECTED_COMMANDS
}

_COMMON_INTENT_FIELDS = (
    "module_id",
    "route_step_index",
    "intent_index",
    "authority_profile_id",
    "source_lot_roots",
)
EXPECTED_INTENT_PAYLOAD_SCHEMAS: Final[dict[str, dict[str, Any]]] = {
    intent_id: {
        "intent_id": intent_id,
        "common_field_ids": list(_COMMON_INTENT_FIELDS),
        "variant_field_ids": list(variant_fields),
        "integer_policy": "CHECKED_NO_FLOAT",
    }
    for intent_id, variant_fields in {
        "AUTHORIZED_BURN": ("asset_id", "amount_atoms"),
        "AUTHORIZED_ISSUE": ("asset_id", "amount_atoms"),
        "CUSTODY_CHANGE": ("asset_id", "amount_atoms", "custody_role"),
        "ESCROW_CHANGE": ("asset_id", "amount_atoms", "escrow_role"),
        "LEDGER_TRANSFER": (
            "asset_id",
            "amount_atoms",
            "source_account_role",
            "destination_account_role",
        ),
        "LIABILITY_CHANGE": ("asset_id", "signed_amount_atoms", "liability_role"),
        "MODULE_RELEASE_LIFECYCLE_CHANGE": (
            "module_id",
            "from_release_id",
            "to_release_id",
            "lifecycle_transition",
            "migration_inventory_root",
        ),
        "NULLIFIER_CONSUME": ("nullifier",),
        "ORACLE_OCCURRENCE_RECORD": ("oracle_occurrence_root",),
        "OUTBOX_ENQUEUE": ("destination_id", "payload_root", "outbox_kind"),
        "POLICY_PROFILE_CHANGE": (
            "from_profile_root",
            "to_profile_root",
            "activation_epoch",
        ),
        "RESERVE_CHANGE": ("asset_id", "signed_amount_atoms", "reserve_role"),
        "TAU_CONNECTIVITY_MODE_CHANGE": (
            "from_mode",
            "to_mode",
            "checkpoint_root",
            "tau_profile_root",
        ),
        "TERMINAL_OBLIGATION_CHANGE": (
            "object_kind",
            "object_id",
            "from_phase",
            "to_phase",
            "terminal_owner",
            "residue_atoms",
        ),
    }.items()
}

CONTRACT_ATOMS: Final = frozenset(
    {
        "ATOMIC_PUBLICATION",
        "ACTIVE_POLICY_EPOCH_BOUND",
        "AUTHENTICATED_CONTEXT",
        "BACKEND_ID_BOUND",
        "CANONICAL_COMMAND",
        "CANONICAL_OUTBOX_ACK",
        "CANONICAL_POLICY_QUERY",
        "CANONICAL_RELEASE_QUERY",
        "CANONICAL_ROUTE_QUERY",
        "CHECKED_INTEGER_DOMAIN",
        "CLOSED_ALLOWED_INTENTS",
        "COMMITTED_OUTBOX_ANCESTRY",
        "CANDIDATE_PUBLICATION_EQUALITY_BOUND",
        "COMPLETE_SOURCE_LOT_LINEAGE",
        "CURRENT_PARENT_ROOT",
        "DERIVED_VALUE_DELTA",
        "DESTINATION_BOUND",
        "DETERMINISTIC_TOTAL_OUTCOME",
        "EXACT_RELEASE_SET",
        "EXECUTION_ADMISSION_BOUND",
        "EXECUTION_COMMITMENTS_BOUND",
        "GLOBAL_RECONCILIATION",
        "GOVERNANCE_AUTHORITY_BOUND",
        "GOVERNANCE_WITNESS_BOUND",
        "GOVERNED_CONTROL_SCOPE_BOUND",
        "INTENT_CAPABILITY_BOUND",
        "JOURNAL_BYTES_BOUND",
        "MODULE_RELEASE_SET_BOUND",
        "NO_EXTERNAL_EFFECT_APPLICATION",
        "OUTBOX_ID_BOUND",
        "OWN_DOMAIN_PROPOSAL_ONLY",
        "PAYLOAD_ROOT_BOUND",
        "POLICY_PROFILE_BOUND",
        "PROOF_IMAGE_ID_BOUND",
        "PROOF_PROFILE_BOUND",
        "PROMOTION_SUBJECT_BOUND",
        "PUBLICATION_ROOT_BOUND",
        "REJECT_EMPTY_PROPOSAL",
        "REJECT_NO_COMMIT",
        "RESOLVED_ROUTE",
        "ROOT_BOUND_REQUIRED_VIEWS",
        "SOURCE_ROOT_BOUND",
        "TERMINAL_OBLIGATIONS_EXPLICIT",
        "TAU_CONNECTIVITY_SCOPE_ONLY",
        "TAU_REPRESENTATION_BOUND",
        "VERIFIED_BACKEND_RECEIPT",
        "VERIFIED_GOVERNANCE_AUTHORIZATION",
        "VERIFIED_POLICY_ADMISSION",
        "VERIFIED_ZRPF_WITNESS",
        "VERIFIER_REGISTRY_BOUND",
        "VERIFIER_EXECUTION_PROFILE_BOUND",
        "WRITER_EPOCH_BOUND",
    }
)


def _port(
    *,
    caller: str,
    callee: str,
    request_type: str,
    response_type: str,
    stage: str,
    multiplicity: str,
    order: str,
    replay_scope: str,
    request_guarantees: tuple[str, ...],
    response_guarantees: tuple[str, ...],
    authority_constructor: str = "NONE",
) -> dict[str, Any]:
    return {
        "caller": caller,
        "callee": callee,
        "request_type": request_type,
        "response_type": response_type,
        "schema_version": 2,
        "stage": stage,
        "multiplicity": multiplicity,
        "order": order,
        "replay_scope": replay_scope,
        "request_guarantees": list(request_guarantees),
        "callee_request_assumptions": list(request_guarantees),
        "response_guarantees": list(response_guarantees),
        "caller_response_assumptions": list(response_guarantees),
        "authority_constructor": authority_constructor,
        "caller_constructible_authority": False,
    }


EXPECTED_PORT_SPECS: Final[dict[str, dict[str, Any]]] = {
    "P_SETTLEMENT_EXECUTION": _port(
        caller="ZENO_LEDGER",
        callee="SETTLEMENT_KERNEL",
        request_type="AuthenticatedExecutionRequestV2",
        response_type="GlobalOutcomeV2",
        stage="AUTHENTICATED",
        multiplicity="ONE_PER_COMMAND",
        order="COMMAND_INDEX_ASCENDING",
        replay_scope="PROMOTION_SUBJECT_PARENT_COMMAND_SENDER_NONCE_EPOCH",
        request_guarantees=(
            "AUTHENTICATED_CONTEXT",
            "CANONICAL_COMMAND",
            "CURRENT_PARENT_ROOT",
            "PROMOTION_SUBJECT_BOUND",
            "WRITER_EPOCH_BOUND",
        ),
        response_guarantees=(
            "DERIVED_VALUE_DELTA",
            "DETERMINISTIC_TOTAL_OUTCOME",
            "GLOBAL_RECONCILIATION",
            "REJECT_NO_COMMIT",
        ),
    ),
    "P_ROUTE_RESOLUTION": _port(
        caller="SETTLEMENT_KERNEL",
        callee="COMMAND_ROUTER",
        request_type="RouteQueryV2",
        response_type="ResolvedRouteV2",
        stage="RESOLUTION",
        multiplicity="ONE_PER_COMMAND",
        order="BEFORE_RELEASE_AND_MODULE_EVALUATION",
        replay_scope="PROMOTION_SUBJECT_COMMAND_ROUTE_REGISTRY",
        request_guarantees=("CANONICAL_ROUTE_QUERY", "PROMOTION_SUBJECT_BOUND"),
        response_guarantees=("RESOLVED_ROUTE", "SOURCE_ROOT_BOUND"),
    ),
    "P_RELEASE_RESOLUTION": _port(
        caller="SETTLEMENT_KERNEL",
        callee="RELEASE_KERNEL",
        request_type="ReleaseQueryV2",
        response_type="ResolvedReleaseSetV2",
        stage="RESOLUTION",
        multiplicity="ONE_PER_COMMAND",
        order="AFTER_ROUTE_BEFORE_POLICY",
        replay_scope="PROMOTION_SUBJECT_PROFILE_ROUTE_CREATOR_RELEASE_EPOCH",
        request_guarantees=(
            "CANONICAL_RELEASE_QUERY",
            "CURRENT_PARENT_ROOT",
            "PROMOTION_SUBJECT_BOUND",
        ),
        response_guarantees=("EXACT_RELEASE_SET", "MODULE_RELEASE_SET_BOUND"),
        authority_constructor="RELEASE_KERNEL_ONLY",
    ),
    "P_POLICY_VERIFICATION": _port(
        caller="SETTLEMENT_KERNEL",
        callee="POLICY_KERNEL",
        request_type="PolicyQueryV2",
        response_type="VerifiedAdmissionV2",
        stage="VERIFICATION",
        multiplicity="ONE_PER_COMMAND",
        order="AFTER_RELEASE_BEFORE_MODULE_EVALUATION",
        replay_scope="OCCURRENCE_PROFILE_RELEASE_SET_VERIFIER_REGISTRY",
        request_guarantees=(
            "ACTIVE_POLICY_EPOCH_BOUND",
            "CANONICAL_POLICY_QUERY",
            "MODULE_RELEASE_SET_BOUND",
            "POLICY_PROFILE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "VERIFIER_EXECUTION_PROFILE_BOUND",
        ),
        response_guarantees=(
            "ACTIVE_POLICY_EPOCH_BOUND",
            "VERIFIED_POLICY_ADMISSION",
            "VERIFIER_EXECUTION_PROFILE_BOUND",
            "VERIFIER_REGISTRY_BOUND",
        ),
        authority_constructor="VERIFIER_ONLY",
    ),
    "P_POLICY_BACKEND": _port(
        caller="POLICY_KERNEL",
        callee="POLICY_VERIFIER_ADAPTER",
        request_type="PolicyBackendQueryV2",
        response_type="PolicyBackendReceiptV2",
        stage="VERIFICATION",
        multiplicity="EXACT_RECEIPT_SET_SELECTED_BY_VERIFIER_PROFILE",
        order="CANONICAL_BACKEND_ID_ASCENDING",
        replay_scope="QUERY_PROFILE_BACKEND_IMPLEMENTATION_TOOLCHAIN",
        request_guarantees=(
            "ACTIVE_POLICY_EPOCH_BOUND",
            "BACKEND_ID_BOUND",
            "CANONICAL_POLICY_QUERY",
            "VERIFIER_EXECUTION_PROFILE_BOUND",
            "VERIFIER_REGISTRY_BOUND",
        ),
        response_guarantees=(
            "ACTIVE_POLICY_EPOCH_BOUND",
            "BACKEND_ID_BOUND",
            "VERIFIED_BACKEND_RECEIPT",
            "VERIFIER_EXECUTION_PROFILE_BOUND",
            "VERIFIER_REGISTRY_BOUND",
        ),
        authority_constructor="VERIFIER_ONLY",
    ),
    "P_ORACLE_VIEW": _port(
        caller="SETTLEMENT_KERNEL",
        callee="ORACLE_MODULE",
        request_type="OracleViewQueryV2",
        response_type="AuthenticatedOracleViewV2",
        stage="VIEW_PROJECTION",
        multiplicity="AT_MOST_ONE_PER_COMMAND",
        order="AFTER_RELEASE_BEFORE_DEPENDENT_MODULE_STEP",
        replay_scope="ORACLE_STATE_ROOT_PROFILE_CONTEXT_OCCURRENCE",
        request_guarantees=(
            "CURRENT_PARENT_ROOT",
            "POLICY_PROFILE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
        ),
        response_guarantees=(
            "POLICY_PROFILE_BOUND",
            "ROOT_BOUND_REQUIRED_VIEWS",
            "SOURCE_ROOT_BOUND",
        ),
        authority_constructor="ORACLE_MODULE_ONLY",
    ),
    "P_TAU_REPRESENTATION_RESOLUTION": _port(
        caller="SETTLEMENT_KERNEL",
        callee="POLICY_KERNEL",
        request_type="TauRepresentationQueryV2",
        response_type="ResolvedTauRepresentationV2",
        stage="RESOLUTION",
        multiplicity="AT_MOST_ONE_PER_TAU_COMMAND",
        order="AFTER_RELEASE_AND_POLICY_BEFORE_TAU_MODULE_EVALUATION",
        replay_scope="PROMOTION_SUBJECT_PROFILE_RELEASE_SET_COMMAND_ASSET",
        request_guarantees=(
            "MODULE_RELEASE_SET_BOUND",
            "POLICY_PROFILE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
        ),
        response_guarantees=(
            "MODULE_RELEASE_SET_BOUND",
            "POLICY_PROFILE_BOUND",
            "TAU_REPRESENTATION_BOUND",
        ),
        authority_constructor="POLICY_KERNEL_ONLY",
    ),
    "P_GOVERNED_CONTROL_INGRESS": _port(
        caller="ZENO_LEDGER",
        callee="SETTLEMENT_KERNEL",
        request_type="GovernedEpochControlV2",
        response_type="GovernedEpochControlOutcomeV2",
        stage="AUTHENTICATED_EPOCH_CONTROL",
        multiplicity="AT_MOST_ONE_PER_BLOCK_BOUNDARY",
        order="BEFORE_FIRST_ECONOMIC_COMMAND_OF_NEW_EPOCH",
        replay_scope="PROMOTION_SUBJECT_PARENT_CONTROL_NONCE_WRITER_EPOCH",
        request_guarantees=(
            "CURRENT_PARENT_ROOT",
            "GOVERNANCE_WITNESS_BOUND",
            "GOVERNED_CONTROL_SCOPE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "WRITER_EPOCH_BOUND",
        ),
        response_guarantees=(
            "ATOMIC_PUBLICATION",
            "DETERMINISTIC_TOTAL_OUTCOME",
            "REJECT_NO_COMMIT",
        ),
    ),
    "P_GOVERNANCE_AUTHORIZATION": _port(
        caller="SETTLEMENT_KERNEL",
        callee="GOVERNANCE_VERIFIER_ADAPTER",
        request_type="GovernanceAuthorizationQueryV2",
        response_type="VerifiedGovernanceAuthorizationV2",
        stage="GOVERNED_CONTROL_AUTHORIZATION",
        multiplicity="EXACTLY_ONE_PER_EPOCH_CONTROL",
        order="BEFORE_RELEASE_OR_POLICY_CONTROL_EVALUATION",
        replay_scope="PROMOTION_SUBJECT_PARENT_CONTROL_GOVERNANCE_REGISTRY_WRITER_EPOCH",
        request_guarantees=(
            "CURRENT_PARENT_ROOT",
            "GOVERNANCE_WITNESS_BOUND",
            "GOVERNED_CONTROL_SCOPE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "WRITER_EPOCH_BOUND",
        ),
        response_guarantees=(
            "GOVERNANCE_AUTHORITY_BOUND",
            "GOVERNED_CONTROL_SCOPE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "VERIFIED_GOVERNANCE_AUTHORIZATION",
            "WRITER_EPOCH_BOUND",
        ),
        authority_constructor="GOVERNANCE_VERIFIER_ONLY",
    ),
    "P_RELEASE_CONTROL": _port(
        caller="SETTLEMENT_KERNEL",
        callee="RELEASE_KERNEL",
        request_type="AuthorizedReleaseControlRequestV2",
        response_type="ModuleOutcomeV2",
        stage="GOVERNED_CONTROL_EVALUATION",
        multiplicity="AT_MOST_ONE_PER_EPOCH_CONTROL",
        order="CONTROL_STEP_INDEX_ASCENDING",
        replay_scope="PROMOTION_SUBJECT_PARENT_CONTROL_RELEASE_SET_EPOCH",
        request_guarantees=(
            "CURRENT_PARENT_ROOT",
            "GOVERNANCE_AUTHORITY_BOUND",
            "GOVERNED_CONTROL_SCOPE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "VERIFIED_GOVERNANCE_AUTHORIZATION",
        ),
        response_guarantees=(
            "CLOSED_ALLOWED_INTENTS",
            "DETERMINISTIC_TOTAL_OUTCOME",
            "INTENT_CAPABILITY_BOUND",
            "OWN_DOMAIN_PROPOSAL_ONLY",
            "REJECT_EMPTY_PROPOSAL",
        ),
        authority_constructor="RELEASE_KERNEL_ONLY",
    ),
    "P_POLICY_CONTROL": _port(
        caller="SETTLEMENT_KERNEL",
        callee="POLICY_KERNEL",
        request_type="AuthorizedPolicyControlRequestV2",
        response_type="ModuleOutcomeV2",
        stage="GOVERNED_CONTROL_EVALUATION",
        multiplicity="AT_MOST_ONE_PER_EPOCH_CONTROL",
        order="CONTROL_STEP_INDEX_ASCENDING",
        replay_scope="PROMOTION_SUBJECT_PARENT_CONTROL_PROFILE_EPOCH",
        request_guarantees=(
            "CURRENT_PARENT_ROOT",
            "GOVERNANCE_AUTHORITY_BOUND",
            "GOVERNED_CONTROL_SCOPE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "VERIFIED_GOVERNANCE_AUTHORIZATION",
        ),
        response_guarantees=(
            "CLOSED_ALLOWED_INTENTS",
            "DETERMINISTIC_TOTAL_OUTCOME",
            "INTENT_CAPABILITY_BOUND",
            "OWN_DOMAIN_PROPOSAL_ONLY",
            "REJECT_EMPTY_PROPOSAL",
        ),
        authority_constructor="POLICY_KERNEL_ONLY",
    ),
    "P_ZRPF_ROOT_INGRESS": _port(
        caller="ZENO_LEDGER",
        callee="SETTLEMENT_KERNEL",
        request_type="ZRPFProofQueryV2",
        response_type="GlobalOutcomeV2",
        stage="AUTHENTICATED_PROOF_ADMISSION",
        multiplicity="AT_MOST_ONE_PER_PROVED_BATCH",
        order="BEFORE_PROOF_VERIFICATION_AND_HEAD_RECHECK",
        replay_scope="PROMOTION_SUBJECT_PARENT_JOURNAL_PROOF_PROFILE_WRITER_EPOCH",
        request_guarantees=(
            "CURRENT_PARENT_ROOT",
            "JOURNAL_BYTES_BOUND",
            "PROOF_IMAGE_ID_BOUND",
            "PROOF_PROFILE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "WRITER_EPOCH_BOUND",
        ),
        response_guarantees=(
            "DERIVED_VALUE_DELTA",
            "DETERMINISTIC_TOTAL_OUTCOME",
            "GLOBAL_RECONCILIATION",
            "REJECT_NO_COMMIT",
        ),
    ),
    "P_ZRPF_PROOF_VERIFICATION": _port(
        caller="SETTLEMENT_KERNEL",
        callee="RISC0_VERIFIER_ADAPTER",
        request_type="ZRPFProofQueryV2",
        response_type="VerifiedZRPFJournalV2",
        stage="PROOF_VERIFICATION",
        multiplicity="EXACTLY_ONE_PER_ZRPF_ROOT_ADMISSION",
        order="AFTER_RELEASE_AND_POLICY_BEFORE_HEAD_RECHECK",
        replay_scope="PROMOTION_SUBJECT_JOURNAL_IMAGE_PROOF_PROFILE_VERIFIER_REGISTRY",
        request_guarantees=(
            "JOURNAL_BYTES_BOUND",
            "MODULE_RELEASE_SET_BOUND",
            "POLICY_PROFILE_BOUND",
            "PROOF_IMAGE_ID_BOUND",
            "PROOF_PROFILE_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "VERIFIER_REGISTRY_BOUND",
        ),
        response_guarantees=(
            "EXECUTION_COMMITMENTS_BOUND",
            "JOURNAL_BYTES_BOUND",
            "PROOF_IMAGE_ID_BOUND",
            "PROOF_PROFILE_BOUND",
            "VERIFIED_ZRPF_WITNESS",
            "VERIFIER_REGISTRY_BOUND",
        ),
        authority_constructor="RISC0_VERIFIER_ONLY",
    ),
    "P_SETTLEMENT_PUBLICATION": _port(
        caller="SETTLEMENT_KERNEL",
        callee="ZENO_LEDGER",
        request_type="AcceptCandidateV2",
        response_type="PublicationBundleV2",
        stage="PUBLICATION",
        multiplicity="AT_MOST_ONE_PER_ACCEPTED_TRANSITION",
        order="AFTER_GLOBAL_RECONCILIATION",
        replay_scope="PROMOTION_SUBJECT_PARENT_CANDIDATE_WRITER_EPOCH",
        request_guarantees=(
            "CURRENT_PARENT_ROOT",
            "DERIVED_VALUE_DELTA",
            "EXECUTION_ADMISSION_BOUND",
            "EXECUTION_COMMITMENTS_BOUND",
            "GLOBAL_RECONCILIATION",
            "PROMOTION_SUBJECT_BOUND",
        ),
        response_guarantees=(
            "ATOMIC_PUBLICATION",
            "CANDIDATE_PUBLICATION_EQUALITY_BOUND",
            "PUBLICATION_ROOT_BOUND",
            "WRITER_EPOCH_BOUND",
        ),
        authority_constructor="ZENO_LEDGER_ONLY",
    ),
    "P_COMMITTED_OUTBOX": _port(
        caller="ZENO_LEDGER",
        callee="OUTBOX_SHELL",
        request_type="CommittedOutboxEnvelopeV2",
        response_type="OutboxDeliveryReceiptV2",
        stage="COMMITTED_EFFECT",
        multiplicity="ZERO_OR_MORE_PER_PUBLICATION",
        order="AFTER_HEAD_COMMIT",
        replay_scope="DESTINATION_OUTBOX_PAYLOAD_PUBLICATION_SUBJECT_EPOCH",
        request_guarantees=(
            "COMMITTED_OUTBOX_ANCESTRY",
            "DESTINATION_BOUND",
            "OUTBOX_ID_BOUND",
            "PAYLOAD_ROOT_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "PUBLICATION_ROOT_BOUND",
            "WRITER_EPOCH_BOUND",
        ),
        response_guarantees=(
            "DESTINATION_BOUND",
            "OUTBOX_ID_BOUND",
            "PAYLOAD_ROOT_BOUND",
            "PUBLICATION_ROOT_BOUND",
        ),
    ),
    "P_OUTBOX_ACK_SUBMISSION": _port(
        caller="OUTBOX_SHELL",
        callee="ZENO_LEDGER",
        request_type="OutboxAckCommandV2",
        response_type="SubmissionReceiptV2",
        stage="SUBSEQUENT_COMMAND_SUBMISSION",
        multiplicity="AT_MOST_ONE_PER_DELIVERY_RECEIPT",
        order="AFTER_DELIVERY_ATTEMPT",
        replay_scope="DESTINATION_OUTBOX_PAYLOAD_PUBLICATION_SUBJECT_EPOCH",
        request_guarantees=(
            "CANONICAL_OUTBOX_ACK",
            "DESTINATION_BOUND",
            "OUTBOX_ID_BOUND",
            "PAYLOAD_ROOT_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "PUBLICATION_ROOT_BOUND",
            "WRITER_EPOCH_BOUND",
        ),
        response_guarantees=(
            "OUTBOX_ID_BOUND",
            "PROMOTION_SUBJECT_BOUND",
            "WRITER_EPOCH_BOUND",
        ),
    ),
}

_MODULE_REQUEST_GUARANTEES = (
    "AUTHENTICATED_CONTEXT",
    "CANONICAL_COMMAND",
    "CURRENT_PARENT_ROOT",
    "MODULE_RELEASE_SET_BOUND",
    "PROMOTION_SUBJECT_BOUND",
    "RESOLVED_ROUTE",
    "ROOT_BOUND_REQUIRED_VIEWS",
    "VERIFIED_POLICY_ADMISSION",
)
_MODULE_RESPONSE_GUARANTEES = (
    "CHECKED_INTEGER_DOMAIN",
    "CLOSED_ALLOWED_INTENTS",
    "COMPLETE_SOURCE_LOT_LINEAGE",
    "DETERMINISTIC_TOTAL_OUTCOME",
    "NO_EXTERNAL_EFFECT_APPLICATION",
    "INTENT_CAPABILITY_BOUND",
    "OWN_DOMAIN_PROPOSAL_ONLY",
    "REJECT_EMPTY_PROPOSAL",
    "TERMINAL_OBLIGATIONS_EXPLICIT",
)
for _module_id in EXPECTED_MODULE_COMMANDS:
    EXPECTED_PORT_SPECS[f"P_{_module_id}_EVALUATION"] = _port(
        caller="SETTLEMENT_KERNEL",
        callee=_module_id,
        request_type="ModuleExecutionRequestV2",
        response_type="ModuleOutcomeV2",
        stage="MODULE_EVALUATION",
        multiplicity="ZERO_OR_MORE_PER_COMMAND_ROUTE",
        order="ROUTE_STEP_INDEX_ASCENDING",
        replay_scope="OCCURRENCE_MODULE_RELEASE_SET_ROUTE_STEP_PRESTATE",
        request_guarantees=_MODULE_REQUEST_GUARANTEES,
        response_guarantees=_MODULE_RESPONSE_GUARANTEES,
    )

EXPECTED_PORT_IDS: Final = frozenset(EXPECTED_PORT_SPECS)


def _module_spec(
    module_id: str,
    *,
    kind: str,
    build_depends_on: tuple[str, ...] = ("SETTLEMENT_ABI",),
    runtime_port_ids: tuple[str, ...] = (),
    local_reads: tuple[str, ...] = (),
    accepted_views: tuple[str, ...] = (),
    allowed_intents: tuple[str, ...] = (),
) -> dict[str, Any]:
    owned = tuple(
        domain_id for domain_id, owner in EXPECTED_STATE_OWNERS.items() if owner == module_id
    )
    return {
        "kind": kind,
        "semantic_version": "2.0.0-candidate",
        "build_depends_on": list(build_depends_on),
        "runtime_port_ids": list(runtime_port_ids),
        "owned_state_domains": list(owned),
        "local_read_state_domains": list(local_reads),
        "proposal_write_domains": list(owned),
        "accepted_view_ids": list(accepted_views),
        "command_ids": list(EXPECTED_MODULE_COMMANDS.get(module_id, ())),
        "allowed_intent_ids": list(allowed_intents),
    }


_ALL_INTENTS = tuple(sorted(EXPECTED_INTENTS))
_ALL_STATE_DOMAINS = tuple(EXPECTED_STATE_OWNERS)
_DOMAIN_VIEWS = ("ECONOMIC_VIEW", "VERIFIED_POLICY_ADMISSION")

EXPECTED_MODULE_SPECS: Final[dict[str, dict[str, Any]]] = {
    "SETTLEMENT_ABI": _module_spec("SETTLEMENT_ABI", kind="ABI", build_depends_on=()),
    "SPOT_LP_MODULE": _module_spec(
        "SPOT_LP_MODULE",
        kind="DOMAIN",
        runtime_port_ids=("P_SPOT_LP_MODULE_EVALUATION",),
        local_reads=("SPOT_LP_STATE",),
        accepted_views=(*_DOMAIN_VIEWS, "AUTHENTICATED_ORACLE_VIEW"),
        allowed_intents=(
            "AUTHORIZED_BURN",
            "AUTHORIZED_ISSUE",
            "LEDGER_TRANSFER",
            "NULLIFIER_CONSUME",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
    ),
    "ORACLE_MODULE": _module_spec(
        "ORACLE_MODULE",
        kind="DOMAIN",
        runtime_port_ids=("P_ORACLE_MODULE_EVALUATION", "P_ORACLE_VIEW"),
        local_reads=("ORACLE_STATE",),
        accepted_views=_DOMAIN_VIEWS,
        allowed_intents=(
            "ESCROW_CHANGE",
            "LEDGER_TRANSFER",
            "NULLIFIER_CONSUME",
            "ORACLE_OCCURRENCE_RECORD",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
    ),
    "ZUSD_MODULE": _module_spec(
        "ZUSD_MODULE",
        kind="DOMAIN",
        runtime_port_ids=("P_ZUSD_MODULE_EVALUATION",),
        local_reads=("ZUSD_STATE",),
        accepted_views=(*_DOMAIN_VIEWS, "AUTHENTICATED_ORACLE_VIEW"),
        allowed_intents=(
            "AUTHORIZED_BURN",
            "AUTHORIZED_ISSUE",
            "CUSTODY_CHANGE",
            "LEDGER_TRANSFER",
            "LIABILITY_CHANGE",
            "NULLIFIER_CONSUME",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
    ),
    "PERPS_MODULE": _module_spec(
        "PERPS_MODULE",
        kind="DOMAIN",
        runtime_port_ids=("P_PERPS_MODULE_EVALUATION",),
        local_reads=("PERPS_STATE",),
        accepted_views=(*_DOMAIN_VIEWS, "AUTHENTICATED_ORACLE_VIEW"),
        allowed_intents=(
            "LEDGER_TRANSFER",
            "LIABILITY_CHANGE",
            "NULLIFIER_CONSUME",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
    ),
    "SELLER_AUCTION_MODULE": _module_spec(
        "SELLER_AUCTION_MODULE",
        kind="DOMAIN",
        runtime_port_ids=("P_SELLER_AUCTION_MODULE_EVALUATION",),
        local_reads=("SELLER_AUCTION_STATE",),
        accepted_views=(*_DOMAIN_VIEWS, "AUTHENTICATED_ORACLE_VIEW"),
        allowed_intents=(
            "ESCROW_CHANGE",
            "LEDGER_TRANSFER",
            "NULLIFIER_CONSUME",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
    ),
    "PRIVATE_SWAP_MODULE": _module_spec(
        "PRIVATE_SWAP_MODULE",
        kind="DOMAIN",
        runtime_port_ids=("P_PRIVATE_SWAP_MODULE_EVALUATION",),
        local_reads=("PRIVATE_SWAP_STATE",),
        accepted_views=_DOMAIN_VIEWS,
        allowed_intents=(
            "ESCROW_CHANGE",
            "LEDGER_TRANSFER",
            "NULLIFIER_CONSUME",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
    ),
    "TAU_ESCROW_MODULE": _module_spec(
        "TAU_ESCROW_MODULE",
        kind="DOMAIN",
        runtime_port_ids=("P_TAU_ESCROW_MODULE_EVALUATION",),
        local_reads=("TAU_ESCROW_STATE",),
        accepted_views=(
            *_DOMAIN_VIEWS,
            "RESOLVED_RELEASE_VIEW",
            "RESOLVED_TAU_REPRESENTATION",
        ),
        allowed_intents=(
            "AUTHORIZED_BURN",
            "AUTHORIZED_ISSUE",
            "CUSTODY_CHANGE",
            "LEDGER_TRANSFER",
            "LIABILITY_CHANGE",
            "NULLIFIER_CONSUME",
            "OUTBOX_ENQUEUE",
            "TAU_CONNECTIVITY_MODE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
    ),
    "PROOF_REWARD_MODULE": _module_spec(
        "PROOF_REWARD_MODULE",
        kind="DOMAIN",
        runtime_port_ids=("P_PROOF_REWARD_MODULE_EVALUATION",),
        local_reads=("PROOF_REWARD_STATE",),
        accepted_views=_DOMAIN_VIEWS,
        allowed_intents=(
            "LEDGER_TRANSFER",
            "NULLIFIER_CONSUME",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
    ),
    "PROTOCOL_FINANCE_MODULE": _module_spec(
        "PROTOCOL_FINANCE_MODULE",
        kind="DOMAIN",
        runtime_port_ids=("P_PROTOCOL_FINANCE_MODULE_EVALUATION",),
        local_reads=("PROTOCOL_FINANCE_STATE",),
        accepted_views=(*_DOMAIN_VIEWS, "AUTHENTICATED_ORACLE_VIEW"),
        allowed_intents=(
            "AUTHORIZED_BURN",
            "ESCROW_CHANGE",
            "LEDGER_TRANSFER",
            "NULLIFIER_CONSUME",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
    ),
    "POLICY_VERIFIER_ADAPTER": _module_spec(
        "POLICY_VERIFIER_ADAPTER",
        kind="ADAPTER",
        runtime_port_ids=("P_POLICY_BACKEND",),
    ),
    "GOVERNANCE_VERIFIER_ADAPTER": _module_spec(
        "GOVERNANCE_VERIFIER_ADAPTER",
        kind="ADAPTER",
        runtime_port_ids=("P_GOVERNANCE_AUTHORIZATION",),
    ),
    "RISC0_VERIFIER_ADAPTER": _module_spec(
        "RISC0_VERIFIER_ADAPTER",
        kind="ADAPTER",
        runtime_port_ids=("P_ZRPF_PROOF_VERIFICATION",),
    ),
    "POLICY_KERNEL": _module_spec(
        "POLICY_KERNEL",
        kind="KERNEL",
        runtime_port_ids=(
            "P_POLICY_BACKEND",
            "P_POLICY_CONTROL",
            "P_POLICY_VERIFICATION",
            "P_TAU_REPRESENTATION_RESOLUTION",
        ),
        local_reads=("POLICY_PROFILE_REGISTRY",),
        allowed_intents=("POLICY_PROFILE_CHANGE",),
    ),
    "RELEASE_KERNEL": _module_spec(
        "RELEASE_KERNEL",
        kind="KERNEL",
        runtime_port_ids=("P_RELEASE_CONTROL", "P_RELEASE_RESOLUTION"),
        local_reads=("RELEASE_SELECTION_MIGRATION",),
        allowed_intents=("MODULE_RELEASE_LIFECYCLE_CHANGE",),
    ),
    "COMMAND_ROUTER": _module_spec(
        "COMMAND_ROUTER", kind="ROUTER", runtime_port_ids=("P_ROUTE_RESOLUTION",)
    ),
    "SETTLEMENT_KERNEL": _module_spec(
        "SETTLEMENT_KERNEL",
        kind="KERNEL",
        runtime_port_ids=tuple(
            sorted(
                {
                    "P_SETTLEMENT_EXECUTION",
                    "P_GOVERNED_CONTROL_INGRESS",
                    "P_GOVERNANCE_AUTHORIZATION",
                    "P_POLICY_CONTROL",
                    "P_ROUTE_RESOLUTION",
                    "P_RELEASE_CONTROL",
                    "P_RELEASE_RESOLUTION",
                    "P_POLICY_VERIFICATION",
                    "P_ORACLE_VIEW",
                    "P_SETTLEMENT_PUBLICATION",
                    "P_TAU_REPRESENTATION_RESOLUTION",
                    "P_ZRPF_PROOF_VERIFICATION",
                    "P_ZRPF_ROOT_INGRESS",
                    *(f"P_{module_id}_EVALUATION" for module_id in EXPECTED_MODULE_COMMANDS),
                }
            )
        ),
        local_reads=_ALL_STATE_DOMAINS,
        allowed_intents=(),
    ),
    "OUTBOX_SHELL": _module_spec(
        "OUTBOX_SHELL",
        kind="SHELL",
        runtime_port_ids=("P_COMMITTED_OUTBOX", "P_OUTBOX_ACK_SUBMISSION"),
        local_reads=(),
    ),
    "ZENO_LEDGER": _module_spec(
        "ZENO_LEDGER",
        kind="WRITER",
        runtime_port_ids=(
            "P_COMMITTED_OUTBOX",
            "P_GOVERNED_CONTROL_INGRESS",
            "P_OUTBOX_ACK_SUBMISSION",
            "P_SETTLEMENT_EXECUTION",
            "P_SETTLEMENT_PUBLICATION",
            "P_ZRPF_ROOT_INGRESS",
        ),
        local_reads=_ALL_STATE_DOMAINS,
    ),
    "RISC0_GUEST": _module_spec(
        "RISC0_GUEST",
        kind="GUEST",
        build_depends_on=("SETTLEMENT_KERNEL",),
    ),
}


_MODULE_ASSET_SCOPES: Final[dict[str, str]] = {
    "SPOT_LP_MODULE": "ROUTE_POOL_ASSETS_OR_LP_SHARE",
    "ORACLE_MODULE": "ORACLE_BOND_ASSET",
    "ZUSD_MODULE": "ZUSD_OR_DECLARED_COLLATERAL_ASSET",
    "PERPS_MODULE": "POSITION_MARGIN_OR_SETTLEMENT_ASSET",
    "SELLER_AUCTION_MODULE": "AUCTION_INVENTORY_OR_BID_ASSET",
    "PRIVATE_SWAP_MODULE": "SWAP_OFFER_OR_REQUEST_ASSET",
    "TAU_ESCROW_MODULE": "TAU_ESCROWED_OR_WRAPPED_ASSET",
    "PROOF_REWARD_MODULE": "ZDEX_PROOF_REWARD_RESERVE",
    "PROTOCOL_FINANCE_MODULE": "ZDEX_OR_ELIGIBLE_SURPLUS_QUOTE_ASSET",
    "POLICY_KERNEL": "NONE",
    "RELEASE_KERNEL": "NONE",
}

_MODULE_ACCOUNT_ROLE_SCOPES: Final[dict[str, tuple[str, ...]]] = {
    "SPOT_LP_MODULE": ("LP_POOL", "LP_POSITION_OWNER", "TRADER"),
    "ORACLE_MODULE": ("ORACLE_BOND_ESCROW", "ORACLE_REPORTER", "ORACLE_SLASH_RESERVE"),
    "ZUSD_MODULE": (
        "BORROWER",
        "COLLATERAL_CUSTODY",
        "STABILITY_POOL",
        "ZUSD_SUPPLY",
    ),
    "PERPS_MODULE": ("INSURANCE_FUND", "MARGIN_CUSTODY", "PERPS_TRADER"),
    "SELLER_AUCTION_MODULE": ("AUCTION_BIDDER", "AUCTION_ESCROW", "AUCTION_SELLER"),
    "PRIVATE_SWAP_MODULE": ("PRIVATE_SWAP_COUNTERPARTY", "PRIVATE_SWAP_ESCROW"),
    "TAU_ESCROW_MODULE": ("TAU_BRIDGE_ESCROW", "TAU_USER", "WRAPPED_ASSET_SUPPLY"),
    "PROOF_REWARD_MODULE": ("PROOF_PROVIDER", "PROOF_REWARD_RESERVE"),
    "PROTOCOL_FINANCE_MODULE": ("PROTOCOL_BURN_RESERVE", "PROTOCOL_TREASURY"),
    "POLICY_KERNEL": (),
    "RELEASE_KERNEL": (),
}

_ISSUE_BURN_SCOPE_OVERRIDES: Final[dict[tuple[str, str], tuple[str, str]]] = {
    ("SPOT_LP_MODULE", "AUTHORIZED_ISSUE"): ("LP_SHARE_ONLY", "LP_SHARE_ISSUER_V2"),
    ("SPOT_LP_MODULE", "AUTHORIZED_BURN"): ("LP_SHARE_ONLY", "LP_SHARE_ISSUER_V2"),
    ("ZUSD_MODULE", "AUTHORIZED_ISSUE"): ("ZUSD_ONLY", "ZUSD_MONETARY_KERNEL_V2"),
    ("ZUSD_MODULE", "AUTHORIZED_BURN"): ("ZUSD_ONLY", "ZUSD_MONETARY_KERNEL_V2"),
    ("TAU_ESCROW_MODULE", "AUTHORIZED_ISSUE"): (
        "TAU_WRAPPED_ASSET_ONLY",
        "TAU_REPRESENTATION_POLICY_V2",
    ),
    ("TAU_ESCROW_MODULE", "AUTHORIZED_BURN"): (
        "TAU_WRAPPED_ASSET_ONLY",
        "TAU_REPRESENTATION_POLICY_V2",
    ),
    ("PROTOCOL_FINANCE_MODULE", "AUTHORIZED_BURN"): (
        "ZDEX_ONLY",
        "ZDEX_BURN_AUTHORITY_V2",
    ),
}


def _intent_capability(module_id: str, intent_id: str) -> dict[str, Any]:
    asset_scope = _MODULE_ASSET_SCOPES[module_id]
    authority_profile = "MODULE_PROPOSAL_SETTLEMENT_RECHECK_V2"
    if (module_id, intent_id) in _ISSUE_BURN_SCOPE_OVERRIDES:
        asset_scope, authority_profile = _ISSUE_BURN_SCOPE_OVERRIDES[(module_id, intent_id)]
    if intent_id in {
        "MODULE_RELEASE_LIFECYCLE_CHANGE",
        "POLICY_PROFILE_CHANGE",
        "TAU_CONNECTIVITY_MODE_CHANGE",
        "TERMINAL_OBLIGATION_CHANGE",
    }:
        asset_scope = "NONE"
    return {
        "module_id": module_id,
        "intent_id": intent_id,
        "asset_scope": asset_scope,
        "account_role_scope": list(_MODULE_ACCOUNT_ROLE_SCOPES[module_id]),
        "authority_profile": authority_profile,
        "settlement_recheck_required": True,
    }


EXPECTED_INTENT_CAPABILITIES: Final[dict[str, dict[str, Any]]] = {
    f"{module_id}:{intent_id}": _intent_capability(module_id, intent_id)
    for module_id, module in EXPECTED_MODULE_SPECS.items()
    for intent_id in module["allowed_intent_ids"]
    if module_id in _MODULE_ASSET_SCOPES
}


def _step(
    index: int,
    module_id: str,
    phase: str,
    depends_on: tuple[int, ...] = (),
    *,
    required_intents: tuple[str, ...] = (),
    optional_intents: tuple[str, ...] = (),
) -> dict[str, Any]:
    return {
        "step_index": index,
        "module_id": module_id,
        "evaluation_port_id": f"P_{module_id}_EVALUATION",
        "phase": phase,
        "depends_on_step_indexes": list(depends_on),
        "required_intent_ids": list(required_intents),
        "optional_intent_ids": list(optional_intents),
    }


def _route(
    module_id: str,
    *,
    required: tuple[str, ...],
    optional: tuple[str, ...] = (),
    views: tuple[str, ...] = _DOMAIN_VIEWS,
    constraints: tuple[str, ...] = ("NO_DUPLICATE_SOURCE_LOT",),
    terminal: str,
    steps: tuple[dict[str, Any], ...] | None = None,
) -> dict[str, Any]:
    actual_steps = steps or (
        _step(
            0,
            module_id,
            "PRIMARY",
            required_intents=required,
            optional_intents=optional,
        ),
    )
    release_participants = {step["module_id"] for step in actual_steps}
    if "AUTHENTICATED_ORACLE_VIEW" in views:
        release_participants.add("ORACLE_MODULE")
    return {
        "primary_module_id": module_id,
        "steps": list(actual_steps),
        "required_view_ids": list(views),
        "release_participant_module_ids": sorted(release_participants),
        "required_intent_ids": list(required),
        "optional_intent_ids": list(optional),
        "constraint_ids": list(constraints),
        "terminal_class": terminal,
    }


_ORACLE_VIEWS = (*_DOMAIN_VIEWS, "AUTHENTICATED_ORACLE_VIEW")
_RELEASE_VIEWS = (*_DOMAIN_VIEWS, "RESOLVED_RELEASE_VIEW")
_TAU_VIEWS = (*_RELEASE_VIEWS, "RESOLVED_TAU_REPRESENTATION")

EXPECTED_ROUTE_SPECS: Final[dict[str, dict[str, Any]]] = {
    "spot_swap": _route(
        "SPOT_LP_MODULE",
        required=("LEDGER_TRANSFER",),
        optional=("RESERVE_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
        constraints=("AT_LEAST_TWO_LEDGER_TRANSFER_LEGS", "NO_DUPLICATE_SOURCE_LOT"),
        terminal="IMMEDIATE",
    ),
    "lp_add": _route(
        "SPOT_LP_MODULE",
        required=("AUTHORIZED_ISSUE", "LEDGER_TRANSFER", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("RESERVE_CHANGE",),
        terminal="LIFECYCLE_CREATE",
    ),
    "lp_remove": _route(
        "SPOT_LP_MODULE",
        required=("AUTHORIZED_BURN", "LEDGER_TRANSFER", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("RESERVE_CHANGE",),
        terminal="TERMINAL_OR_PARTIAL",
    ),
    "oracle_submit": _route(
        "ORACLE_MODULE",
        required=(
            "ESCROW_CHANGE",
            "LEDGER_TRANSFER",
            "ORACLE_OCCURRENCE_RECORD",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
        optional=("NULLIFIER_CONSUME", "RESERVE_CHANGE"),
        terminal="LIFECYCLE_CREATE_OR_UPDATE",
    ),
    "oracle_dispute": _route(
        "ORACLE_MODULE",
        required=("ESCROW_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
        optional=(
            "LEDGER_TRANSFER",
            "NULLIFIER_CONSUME",
            "ORACLE_OCCURRENCE_RECORD",
            "RESERVE_CHANGE",
        ),
        terminal="LIFECYCLE_UPDATE_OR_TERMINAL",
    ),
    "zusd_borrow": _route(
        "ZUSD_MODULE",
        required=(
            "AUTHORIZED_ISSUE",
            "LEDGER_TRANSFER",
            "LIABILITY_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
        optional=("CUSTODY_CHANGE", "RESERVE_CHANGE"),
        views=_ORACLE_VIEWS,
        terminal="LIFECYCLE_CREATE",
    ),
    "zusd_repay": _route(
        "ZUSD_MODULE",
        required=("AUTHORIZED_BURN", "LIABILITY_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("CUSTODY_CHANGE", "LEDGER_TRANSFER", "RESERVE_CHANGE"),
        terminal="LIFECYCLE_UPDATE_OR_TERMINAL",
    ),
    "zusd_redeem": _route(
        "ZUSD_MODULE",
        required=(
            "AUTHORIZED_BURN",
            "LEDGER_TRANSFER",
            "LIABILITY_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
        optional=("CUSTODY_CHANGE", "RESERVE_CHANGE"),
        views=_ORACLE_VIEWS,
        terminal="LIFECYCLE_UPDATE_OR_TERMINAL",
    ),
    "zusd_liquidate": _route(
        "ZUSD_MODULE",
        required=(
            "AUTHORIZED_BURN",
            "LEDGER_TRANSFER",
            "LIABILITY_CHANGE",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
        optional=("CUSTODY_CHANGE",),
        views=_ORACLE_VIEWS,
        terminal="TERMINAL",
    ),
    "zusd_redistribute": _route(
        "ZUSD_MODULE",
        required=("LEDGER_TRANSFER", "LIABILITY_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("RESERVE_CHANGE",),
        views=_ORACLE_VIEWS,
        terminal="LIFECYCLE_UPDATE",
    ),
    "stability_pool_deposit": _route(
        "ZUSD_MODULE",
        required=("LEDGER_TRANSFER", "LIABILITY_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("RESERVE_CHANGE",),
        terminal="LIFECYCLE_CREATE_OR_UPDATE",
    ),
    "stability_pool_withdraw": _route(
        "ZUSD_MODULE",
        required=("LEDGER_TRANSFER", "LIABILITY_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("RESERVE_CHANGE",),
        terminal="LIFECYCLE_UPDATE_OR_TERMINAL",
    ),
    "perp_open": _route(
        "PERPS_MODULE",
        required=("LEDGER_TRANSFER", "LIABILITY_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("RESERVE_CHANGE",),
        views=_ORACLE_VIEWS,
        terminal="LIFECYCLE_CREATE",
    ),
    "perp_close": _route(
        "PERPS_MODULE",
        required=("LEDGER_TRANSFER", "LIABILITY_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("RESERVE_CHANGE",),
        views=_ORACLE_VIEWS,
        terminal="TERMINAL",
    ),
    "perp_funding": _route(
        "PERPS_MODULE",
        required=("LEDGER_TRANSFER", "LIABILITY_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("RESERVE_CHANGE",),
        views=_ORACLE_VIEWS,
        terminal="LIFECYCLE_UPDATE",
    ),
    "perp_liquidate": _route(
        "PERPS_MODULE",
        required=(
            "LEDGER_TRANSFER",
            "LIABILITY_CHANGE",
            "RESERVE_CHANGE",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
        views=_ORACLE_VIEWS,
        terminal="TERMINAL",
    ),
}

for _prefix, _module_id in (
    ("seller_auction", "SELLER_AUCTION_MODULE"),
    ("private_swap", "PRIVATE_SWAP_MODULE"),
):
    _views = _DOMAIN_VIEWS
    EXPECTED_ROUTE_SPECS[f"{_prefix}_commit"] = _route(
        _module_id,
        required=(
            "ESCROW_CHANGE",
            "LEDGER_TRANSFER",
            "NULLIFIER_CONSUME",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
        views=_views,
        terminal="LIFECYCLE_CREATE",
    )
    EXPECTED_ROUTE_SPECS[f"{_prefix}_reveal"] = _route(
        _module_id,
        required=("NULLIFIER_CONSUME", "TERMINAL_OBLIGATION_CHANGE"),
        views=_views,
        terminal="LIFECYCLE_UPDATE",
    )
    EXPECTED_ROUTE_SPECS[f"{_prefix}_settle"] = _route(
        _module_id,
        required=(
            "ESCROW_CHANGE",
            "LEDGER_TRANSFER",
            "NULLIFIER_CONSUME",
            "TERMINAL_OBLIGATION_CHANGE",
        ),
        optional=("RESERVE_CHANGE",),
        views=_views,
        terminal="TERMINAL",
    )
    EXPECTED_ROUTE_SPECS[f"{_prefix}_cancel"] = _route(
        _module_id,
        required=("ESCROW_CHANGE", "LEDGER_TRANSFER", "TERMINAL_OBLIGATION_CHANGE"),
        views=_views,
        terminal="TERMINAL",
    )
    EXPECTED_ROUTE_SPECS[f"{_prefix}_expire"] = _route(
        _module_id,
        required=("ESCROW_CHANGE", "LEDGER_TRANSFER", "TERMINAL_OBLIGATION_CHANGE"),
        optional=("RESERVE_CHANGE",),
        views=_views,
        terminal="TERMINAL",
    )

EXPECTED_ROUTE_SPECS.update(
    {
        "tau_escrow_deposit": _route(
            "TAU_ESCROW_MODULE",
            required=("CUSTODY_CHANGE", "NULLIFIER_CONSUME", "TERMINAL_OBLIGATION_CHANGE"),
            optional=("AUTHORIZED_ISSUE", "LEDGER_TRANSFER"),
            views=_TAU_VIEWS,
            constraints=(
                "EXACTLY_ONE_TAU_DEPOSIT_REPRESENTATION_LANE",
                "NO_DUPLICATE_SOURCE_LOT",
            ),
            terminal="LIFECYCLE_CREATE",
        ),
        "tau_withdrawal": _route(
            "TAU_ESCROW_MODULE",
            required=(
                "CUSTODY_CHANGE",
                "LIABILITY_CHANGE",
                "OUTBOX_ENQUEUE",
                "TERMINAL_OBLIGATION_CHANGE",
            ),
            optional=("AUTHORIZED_BURN", "LEDGER_TRANSFER", "NULLIFIER_CONSUME"),
            views=_TAU_VIEWS,
            constraints=(
                "EXACTLY_ONE_TAU_WITHDRAWAL_REPRESENTATION_LANE",
                "NO_DUPLICATE_SOURCE_LOT",
            ),
            terminal="LIFECYCLE_CREATE",
        ),
        "tau_withdrawal_ack": _route(
            "TAU_ESCROW_MODULE",
            required=("CUSTODY_CHANGE", "LIABILITY_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
            optional=("LEDGER_TRANSFER", "NULLIFIER_CONSUME"),
            views=_TAU_VIEWS,
            terminal="TERMINAL",
        ),
        "fallback_activate": _route(
            "TAU_ESCROW_MODULE",
            required=("TAU_CONNECTIVITY_MODE_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
            views=_RELEASE_VIEWS,
            terminal="LIFECYCLE_UPDATE",
        ),
        "tau_rejoin": _route(
            "TAU_ESCROW_MODULE",
            required=("TAU_CONNECTIVITY_MODE_CHANGE", "TERMINAL_OBLIGATION_CHANGE"),
            views=_RELEASE_VIEWS,
            terminal="LIFECYCLE_UPDATE",
        ),
        "zrpf_prover_reward": _route(
            "PROOF_REWARD_MODULE",
            required=(
                "LEDGER_TRANSFER",
                "NULLIFIER_CONSUME",
                "RESERVE_CHANGE",
                "TERMINAL_OBLIGATION_CHANGE",
            ),
            terminal="IMMEDIATE",
        ),
        "protocol_buy_and_burn": _route(
            "PROTOCOL_FINANCE_MODULE",
            required=(
                "AUTHORIZED_BURN",
                "LEDGER_TRANSFER",
                "RESERVE_CHANGE",
                "TERMINAL_OBLIGATION_CHANGE",
            ),
            optional=("ESCROW_CHANGE", "NULLIFIER_CONSUME"),
            views=_ORACLE_VIEWS,
            constraints=(
                "AT_LEAST_TWO_LEDGER_TRANSFER_LEGS",
                "NO_DUPLICATE_SOURCE_LOT",
                "SURPLUS_PRIORITY_AND_BURN_FLOOR",
            ),
            terminal="IMMEDIATE",
            steps=(
                _step(
                    0,
                    "PROTOCOL_FINANCE_MODULE",
                    "AUTHORIZE_SURPLUS_BUDGET",
                    required_intents=("RESERVE_CHANGE",),
                    optional_intents=("ESCROW_CHANGE", "NULLIFIER_CONSUME"),
                ),
                _step(
                    1,
                    "SPOT_LP_MODULE",
                    "ACQUIRE_ZDEX",
                    (0,),
                    required_intents=("LEDGER_TRANSFER",),
                ),
                _step(
                    2,
                    "PROTOCOL_FINANCE_MODULE",
                    "AUTHORIZE_BURN",
                    (1,),
                    required_intents=("AUTHORIZED_BURN", "TERMINAL_OBLIGATION_CHANGE"),
                ),
            ),
        ),
    }
)

REQUIRED_OCCURRENCE_FIELDS: Final = frozenset(
    {
        "COMMAND_ID",
        "COMMAND_INDEX",
        "COMMAND_ROOT",
        "CONTEXT_ROOT",
        "DEPLOYMENT_ROOT",
        "MODULE_REGISTRY_ROOT",
        "MODULE_RELEASE_SET_ROOT",
        "NONCE",
        "PARENT_STATE_ROOT",
        "PROFILE_ROOT",
        "PROMOTION_SUBJECT_ROOT",
        "ROUTE_ID",
        "SENDER",
        "WRITER_EPOCH",
    }
)
_ZRPF_COMMITMENT_FIELDS: Final = {
    "EFFECT_PLAN_ROOT": "effect_plan_root",
    "HISTORY_ROOT": "history_root",
    "MODULE_RELEASE_SET_ROOT": "module_release_set_root",
    "NULLIFIER_ROOT": "nullifier_root",
    "OUTBOX_ROOT": "outbox_root",
    "PARENT_STATE_ROOT": "parent_state_root",
    "POLICY_PROFILE_ROOT": "policy_profile_root",
    "POST_STATE_ROOT": "post_state_root",
    "PRE_STATE_ROOT": "pre_state_root",
    "PROMOTION_SUBJECT_ROOT": "promotion_subject_root",
    "VALUE_DELTA_ROOT": "value_delta_root",
    "WRITER_EPOCH": "writer_epoch",
}
EXPECTED_ZRPF_BINDING_SCHEMA_PATHS: Final[dict[str, tuple[str, ...]]] = {
    token: (
        f"ExecutionAdmissionV2.commitments.{field_id}",
        (
            "ExecutionAdmissionV2.verified_zrpf_journal.journal.commitments."
            f"{field_id}"
        ),
    )
    for token, field_id in _ZRPF_COMMITMENT_FIELDS.items()
}
EXPECTED_ZRPF_BINDING_SCHEMA_PATHS.update(
    {
        "IMAGE_ID": (
            "ExecutionAdmissionV2.proof_record.image_id",
            "ExecutionAdmissionV2.verified_zrpf_journal.witness.image_id",
        ),
        "JOURNAL_ROOT": (
            "ExecutionAdmissionV2.proof_record.journal_root",
            "ExecutionAdmissionV2.verified_zrpf_journal.witness.journal_root",
            "ExecutionAdmissionV2.verified_zrpf_journal.exact_journal_bytes_root",
        ),
        "PROOF_ROOT": (
            "ExecutionAdmissionV2.proof_record.proof_root",
            "ExecutionAdmissionV2.verified_zrpf_journal.witness.proof_root",
        ),
        "PROMOTION_SUBJECT_ROOT": (
            "ExecutionAdmissionV2.commitments.promotion_subject_root",
            (
                "ExecutionAdmissionV2.verified_zrpf_journal.journal.commitments."
                "promotion_subject_root"
            ),
            "ExecutionAdmissionV2.verified_zrpf_journal.witness.promotion_subject_root",
        ),
        "VERIFIER_PROFILE_ROOT": (
            "ExecutionAdmissionV2.proof_record.verifier_profile_root",
            "ExecutionAdmissionV2.verified_zrpf_journal.witness.verifier_profile_root",
            "ExecutionAdmissionV2.verified_zrpf_journal.journal.verifier_profile_root",
        ),
        "VERIFIER_REGISTRY_ROOT": (
            "ExecutionAdmissionV2.proof_record.verifier_registry_root",
            "ExecutionAdmissionV2.verified_zrpf_journal.witness.verifier_registry_root",
        ),
        "VERIFIED_WITNESS_ID": (
            "ExecutionAdmissionV2.proof_record.verified_witness_id",
            "ExecutionAdmissionV2.verified_zrpf_journal.witness.opaque_witness_id",
        ),
    }
)
REQUIRED_ZRPF_ADMISSION_BINDING_FIELDS: Final = frozenset(
    EXPECTED_ZRPF_BINDING_SCHEMA_PATHS
)
REQUIRED_RELEASE_LIFECYCLE: Final = (
    "CANDIDATE",
    "SHADOW",
    "ACTIVE_NEW",
    "DRAIN_ONLY",
    "VERIFY_ONLY",
    "RETIRED",
    "REVOKED",
)
REQUIRED_MIGRATION_CLASSES: Final = frozenset(
    {"CLOSED", "MIGRATED", "RETAINED_PINNED", "TOMBSTONED_ZERO_LIABILITY"}
)
REQUIRED_MIGRATION_OBJECT_KINDS: Final = frozenset(
    {
        "LP_POSITION",
        "PERPS_FUNDING_ACCUMULATOR",
        "PERPS_INSURANCE_FUND",
        "PERPS_MARKET",
        "ORACLE_OCCURRENCE_OR_DISPUTE",
        "PERP_POSITION",
        "PRIVATE_SWAP",
        "PROOF_REWARD_CLAIM",
        "PROOF_REWARD_RESERVE",
        "PROTOCOL_BURN_OBLIGATION",
        "PROTOCOL_TREASURY_BURN_RESERVE",
        "SELLER_AUCTION",
        "SPOT_POOL",
        "STABILITY_POOL_GLOBAL_STATE",
        "STABILITY_POOL_POSITION",
        "TAU_CONNECTIVITY_MODE",
        "TAU_ESCROW_OR_WITHDRAWAL",
        "ZUSD_POSITION",
    }
)
REQUIRED_VERIFIER_BACKENDS: Final = frozenset({"NATIVE", "TAU"})
REQUIRED_VERIFIER_REGISTRY_FIELDS: Final = frozenset(
    {
        "BACKEND_ID",
        "CANONICAL_CODEC_ROOT",
        "IMPLEMENTATION_ROOT",
        "QUERY_SCHEMA_ROOT",
        "RESULT_SCHEMA_ROOT",
        "SIGNING_AUTHORITY_ROOT",
        "PROFILE_ROOT",
        "SOURCE_ROOT",
        "TOOLCHAIN_ROOT",
    }
)
REQUIRED_EVIDENCE_RECEIPT_FIELDS: Final = frozenset(
    {
        "ARTIFACT_ROOT",
        "CANDIDATE_ROOT",
        "CLAIM_ID",
        "CONTEXT_ROOT",
        "ISSUER_ID",
        "MODULE_RELEASE_SET_ROOT",
        "OBLIGATION_OCCURRENCE_ROOT",
        "PARENT_STATE_ROOT",
        "PROFILE_ROOT",
        "PROMOTION_SUBJECT_ROOT",
        "QUERY_ROOT",
        "RECEIPT_KIND",
        "REPLAY_COMMAND_ROOT",
        "RESULT",
        "RESULT_ROOT",
        "SIGNATURE_OR_REPLAY_OUTPUT_ROOT",
        "SOURCE_ROOT",
        "TOOLCHAIN_ROOT",
        "VERIFIER_REGISTRY_ROOT",
        "VERIFIER_ID",
        "WRITER_EPOCH",
    }
)

EVIDENCE_GATES: Final[dict[str, tuple[int, str]]] = {
    "COMMAND_ROUTE_CLOSURE": (3, "CHECKED_EXACT_V2"),
    "STATE_OWNERSHIP_AND_WRITE_CONFINEMENT": (3, "CHECKED_EXACT_V2"),
    "DEPENDENCIES_HAVE_TYPED_PORTS": (3, "CHECKED_EXACT_V2"),
    "PORT_CONTRACT_EXACTNESS": (2, "CHECKED_EXACT_V2"),
    "PORT_SEMANTIC_IMPLICATION_DUAL_SOLVER": (4, "DECLARED_PENDING_FORMAL_EVIDENCE"),
    "ESSO_DUAL_SOLVER_COMPOSITION": (4, "DECLARED_PENDING_FORMAL_EVIDENCE"),
    "LEAN_GLOBAL_FOLD_REFINEMENT": (4, "DECLARED_PENDING_FORMAL_EVIDENCE"),
    "MIGRATION_TOTALITY_CONTRACT": (3, "DECLARED_PENDING_RELEASE_EDGE"),
    "VERIFIER_AND_EVIDENCE_BINDING": (3, "DECLARED_PENDING_IMPLEMENTATION_RECEIPTS"),
    "EXTERNAL_EFFECT_ANCESTRY": (3, "CHECKED_EXACT_V2"),
    "DIRECT_ZRPF_API_IDENTITY": (3, "DECLARED_PENDING_IMPLEMENTATION_RECEIPTS"),
    "GOVERNED_CONTROL_ATOMICITY": (4, "DECLARED_PENDING_FORMAL_EVIDENCE"),
    "GOVERNANCE_AUTHORIZATION_BINDING": (4, "DECLARED_PENDING_IMPLEMENTATION_RECEIPTS"),
    "NO_BYPASS_BUILD_INVENTORY": (3, "DECLARED_PENDING_BUILD_INVENTORY"),
}

EXPECTED_MUTANTS: Final = frozenset(
    {
        "ACK_MUTATES_FROM_SHELL",
        "ACK_EPOCH_OMITTED",
        "ADVISORY_SELECTION",
        "ASSUMPTION_TOKEN_INVENTED",
        "CALLER_CONSTRUCTED_AUTHORITY",
        "CALLER_CONSTRUCTED_GOVERNANCE_AUTHORITY",
        "COMMAND_OMITTED",
        "COMMAND_ORDER_AFTER_MODULE_ORDER",
        "COMMAND_WRONG_MODULE",
        "DEPENDENCY_CYCLE",
        "DIRECT_GUEST_CORE_MISMATCH",
        "DIRECT_CARRIES_ZRPF_WITNESS",
        "DRAIN_CREATES_OBJECT",
        "EPOCH_CONTROL_UNTYPED",
        "EXTERNAL_EFFECT_BEFORE_COMMIT",
        "FOREIGN_PROPOSAL_WRITE",
        "GOVERNANCE_WITNESS_DROPPED_DOWNSTREAM",
        "ISSUE_WRONG_ASSET",
        "BURN_WRONG_ASSET",
        "MIGRATION_CLASS_OMITTED",
        "MIGRATION_OBJECT_KIND_OMITTED",
        "NATIVE_BACKUP_WITHOUT_GOVERNANCE_OR_EQUIVALENCE",
        "OCCURRENCE_OMITS_RELEASE_SET",
        "OUTBOX_ID_OMITS_PUBLICATION",
        "ACK_BYPASSES_SETTLEMENT",
        "PORT_ASSUMPTION_NOT_GUARANTEED",
        "PORT_ORDER_ARRIVAL",
        "PORT_TYPE_ANY",
        "PUBLICATION_DUPLICATE_BINDING",
        "RELEASE_CONTROL_BYPASS",
        "POLICY_RELEASE_PARTIAL_COMMIT",
        "ROUTE_STEP_STEALS_INTENT",
        "ROUTE_INTENT_EXCEEDS_CAPABILITY",
        "SECOND_DURABLE_WRITER",
        "SELF_ATTESTED_EVIDENCE",
        "SOLVER_UNKNOWN_ACCEPTED",
        "SOURCE_SPLIT_SNAPSHOT",
        "SOURCE_SYMLINK_SUBSTITUTION",
        "SOURCE_EXECUTION_SNAPSHOT_SPLIT",
        "TRUST_MODULE_DELTA",
        "TAU_ESCALATES_TO_RELEASE_CONTROL",
        "TAU_REPRESENTATION_UNRESOLVED",
        "TAU_FAILOVER_UNGOVERNED",
        "TAU_FAILOVER_PER_QUERY_SWITCH",
        "TAU_QUANTITY_CONTRACT_OMITTED",
        "TRANSFER_WRONG_CUSTODY_ROLE",
        "UNPORTED_DEPENDENCY",
        "UNKNOWN_INTENT",
        "VERIFIER_MISMATCH_FAILS_OPEN",
        "VERIFIER_PROFILE_SUBSTITUTION",
        "ZRPF_BYPASSES_SHARED_COMMIT",
        "ZRPF_BINDING_PATH_UNREALIZABLE",
        "ZRPF_WITNESS_OMITTED",
        "ZRPF_WITNESS_CANDIDATE_SUBSTITUTION",
    }
)

EXPECTED_VIEW_SPECS: Final[dict[str, dict[str, Any]]] = {
    "AUTHENTICATED_ORACLE_VIEW": {
        "provider": "ORACLE_MODULE",
        "value_type": "AuthenticatedOracleViewV2",
        "root_bound": True,
        "mutable": False,
    },
    "ECONOMIC_VIEW": {
        "provider": "SETTLEMENT_KERNEL",
        "value_type": "EconomicViewV2",
        "root_bound": True,
        "mutable": False,
    },
    "RESOLVED_RELEASE_VIEW": {
        "provider": "RELEASE_KERNEL",
        "value_type": "ResolvedReleaseSetV2",
        "root_bound": True,
        "mutable": False,
    },
    "RESOLVED_TAU_REPRESENTATION": {
        "provider": "POLICY_KERNEL",
        "value_type": "ResolvedTauRepresentationV2",
        "root_bound": True,
        "mutable": False,
    },
    "VERIFIED_POLICY_ADMISSION": {
        "provider": "POLICY_KERNEL",
        "value_type": "VerifiedAdmissionV2",
        "root_bound": True,
        "mutable": False,
    },
}

EXPECTED_ROUTE_CONSTRAINT_SPECS: Final[dict[str, str]] = {
    "AT_LEAST_TWO_LEDGER_TRANSFER_LEGS": (
        "An accepted spot swap has at least one input debit and one output credit."
    ),
    "EXACTLY_ONE_TAU_DEPOSIT_REPRESENTATION_LANE": (
        "A Tau deposit selects exactly one governed representation lane: transfer or issue."
    ),
    "EXACTLY_ONE_TAU_WITHDRAWAL_REPRESENTATION_LANE": (
        "A Tau withdrawal selects exactly one governed representation lane: transfer or burn."
    ),
    "NO_DUPLICATE_SOURCE_LOT": (
        "One source lot cannot fund two intents in the same accepted occurrence."
    ),
    "SURPLUS_PRIORITY_AND_BURN_FLOOR": (
        "A burn consumes only policy-eligible surplus after named liabilities and preserves the atom floor."
    ),
}

EXPECTED_DRAIN_ALLOWLIST: Final[dict[str, tuple[str, ...]]] = {
    "SPOT_LP_MODULE": ("lp_remove",),
    "ORACLE_MODULE": ("oracle_dispute",),
    "ZUSD_MODULE": (
        "stability_pool_withdraw",
        "zusd_liquidate",
        "zusd_redeem",
        "zusd_redistribute",
        "zusd_repay",
    ),
    "PERPS_MODULE": ("perp_close", "perp_funding", "perp_liquidate"),
    "SELLER_AUCTION_MODULE": (
        "seller_auction_cancel",
        "seller_auction_expire",
        "seller_auction_reveal",
        "seller_auction_settle",
    ),
    "PRIVATE_SWAP_MODULE": (
        "private_swap_cancel",
        "private_swap_expire",
        "private_swap_reveal",
        "private_swap_settle",
    ),
    "TAU_ESCROW_MODULE": (
        "tau_withdrawal",
        "tau_withdrawal_ack",
    ),
    "PROOF_REWARD_MODULE": ("zrpf_prover_reward",),
    "PROTOCOL_FINANCE_MODULE": (),
}

EXPECTED_COMPOSITION: Final[dict[str, Any]] = {
    "batch_command_order": "COMMAND_INDEX_ASCENDING",
    "route_step_order": "TOPOLOGICAL_THEN_MODULE_ID_ASCENDING",
    "route_step_tie_break": "MODULE_ID_ASCENDING",
    "intent_order": "ROUTE_STEP_INDEX_THEN_MODULE_ID_THEN_INTENT_INDEX",
    "fold_state_source": "EVOLVING_STAGED_CANDIDATE",
    "intent_application": "SETTLEMENT_KERNEL_CHECKED_SEQUENTIAL",
    "source_lot_uniqueness": "ONE_CONSUMPTION_PER_OCCURRENCE",
    "commit_protocol": "ONE_EXPECTED_HEAD_CAS",
    "reject_state_change": "EXACT_NONE",
    "reject_effect_count": 0,
    "value_delta_source": "DERIVED_FROM_STAGED_PRE_POST",
    "module_delta_authoritative": False,
    "release_lifecycle": list(REQUIRED_RELEASE_LIFECYCLE),
    "drain_allowlist": [
        {"module_id": module_id, "command_ids": list(command_ids)}
        for module_id, command_ids in EXPECTED_DRAIN_ALLOWLIST.items()
    ],
    "drain_primary_object_creation_allowed": False,
    "drain_terminal_child_contract": {
        "allowed_routes": [
            {
                "command_id": "tau_withdrawal",
                "creator_release_pin_required": True,
                "module_id": "TAU_ESCROW_MODULE",
                "object_kind": "TAU_ESCROW_OR_WITHDRAWAL",
            }
        ],
        "liability_nonincrease_required": True,
        "must_advance_terminal_reachability": True,
    },
    "objects_pin_creator_release": True,
    "occurrence_identity_fields": sorted(REQUIRED_OCCURRENCE_FIELDS),
    "epoch_control_type": "GovernedEpochControlV2",
    "epoch_control_commit_capability": "ZENO_LEDGER_SUBMIT_V2",
    "authoritative_input_sum": {
        "type": "AuthoritativeInputV2",
        "variants": [
            {
                "id": "ECONOMIC_COMMAND",
                "payload_type": "AuthenticatedExecutionRequestV2",
                "closed_member_count": 33,
                "ingress_port_id": "P_SETTLEMENT_EXECUTION",
            },
            {
                "id": "GOVERNED_EPOCH_CONTROL",
                "payload_type": "GovernedEpochControlV2",
                "closed_member_count": 3,
                "ingress_port_id": "P_GOVERNED_CONTROL_INGRESS",
            },
            {
                "id": "ZRPF_BATCH_PROOF",
                "payload_type": "ZRPFProofQueryV2",
                "closed_member_count": 1,
                "ingress_port_id": "P_ZRPF_ROOT_INGRESS",
            },
        ],
        "other_authoritative_inputs_allowed": False,
    },
    "epoch_control_contract": {
        "authorization_port_id": "P_GOVERNANCE_AUTHORIZATION",
        "authorization_witness_type": "VerifiedGovernanceAuthorizationV2",
        "authorization_constructor": "GOVERNANCE_VERIFIER_ONLY",
        "allowed_changes": [
            {
                "control_variant": "MODULE_RELEASE_LIFECYCLE",
                "intent_id": "MODULE_RELEASE_LIFECYCLE_CHANGE",
                "owner": "RELEASE_KERNEL",
                "port_id": "P_RELEASE_CONTROL",
                "request_type": "AuthorizedReleaseControlRequestV2",
                "write_domain": "RELEASE_SELECTION_MIGRATION",
            },
            {
                "control_variant": "POLICY_PROFILE",
                "intent_id": "POLICY_PROFILE_CHANGE",
                "owner": "POLICY_KERNEL",
                "port_id": "P_POLICY_CONTROL",
                "request_type": "AuthorizedPolicyControlRequestV2",
                "write_domain": "POLICY_PROFILE_REGISTRY",
            },
        ],
        "economic_command_registry_unchanged": True,
        "evaluation_order": ["P_RELEASE_CONTROL", "P_POLICY_CONTROL"],
        "at_least_one_change_required": True,
        "at_most_one_change_per_owner": True,
        "tau_connectivity_change_forbidden": True,
        "publication_port_id": "P_SETTLEMENT_PUBLICATION",
        "commit_capability": "ZENO_LEDGER_SUBMIT_V2",
        "partial_commit_possible": False,
        "reject_state_change": "EXACT_NONE",
        "reject_effect_count": 0,
    },
    "migration": {
        "source_inventory_root_required": True,
        "matrix_key": "OBJECT_KIND_X_ENABLED_RELEASE_EDGE",
        "object_kind_registry": sorted(REQUIRED_MIGRATION_OBJECT_KINDS),
        "enabled_release_edges": [],
        "matrix_rows": [],
        "matrix_status": "UNRESOLVED_NO_ENABLED_RELEASE_EDGE",
        "total_partition_required": True,
        "classification_variants": sorted(REQUIRED_MIGRATION_CLASSES),
        "liability_reconciliation_required": True,
        "old_release_terminal_route_required": True,
    },
    "verifier": {
        "backends": sorted(REQUIRED_VERIFIER_BACKENDS),
        "execution_profile_type": "VerifierExecutionProfileV2",
        "active_profile_state_domain": "POLICY_PROFILE_REGISTRY",
        "active_profile_owner": "POLICY_KERNEL",
        "profile_change_port_id": "P_POLICY_CONTROL",
        "backend_selection_source": "EPOCH_BOUND_VERIFIED_PROFILE",
        "per_query_backend_override_allowed": False,
        "registry_entry_fields": sorted(REQUIRED_VERIFIER_REGISTRY_FIELDS),
        "backend_registry_entries": [],
        "registry_status": "UNRESOLVED_NO_IMPLEMENTATION_RECEIPTS",
        "registry_root_required": True,
        "profile_binding_required": True,
        "mismatch_policy": "REJECT",
        "unknown_timeout_policy": "REJECT",
        "execution_profiles": [
            {
                "id": "NATIVE_ONLY",
                "required_backend_ids": ["NATIVE"],
                "fallback_backend_ids": [],
                "allowed_active_modes": ["NATIVE"],
                "equivalence_receipt_required": False,
            },
            {
                "id": "NATIVE_AND_TAU",
                "required_backend_ids": ["NATIVE", "TAU"],
                "fallback_backend_ids": [],
                "allowed_active_modes": ["NATIVE_AND_TAU"],
                "equivalence_receipt_required": True,
            },
            {
                "id": "TAU_PRIMARY_NATIVE_GOVERNED_FAILOVER",
                "normal_backend_ids": ["TAU"],
                "outage_backend_ids": ["NATIVE"],
                "allowed_active_modes": ["TAU_PRIMARY", "NATIVE_BACKUP"],
                "native_backup_activation_authority": "GOVERNED_POLICY_CONTROL_ONLY",
                "governed_mode_switch_required": True,
                "same_profile_equivalence_receipt_required": True,
                "silent_per_query_fallback_allowed": False,
            },
        ],
        "implicit_backend_fallback_allowed": False,
        "required_receipt_set_exact": True,
        "witness_constructor": "VERIFIER_ONLY",
        "evidence_receipt_fields": sorted(REQUIRED_EVIDENCE_RECEIPT_FIELDS),
        "evidence_grade_source": "DERIVED_FROM_AUTHENTICATED_RECEIPT_KIND_AND_REPLAY",
        "self_attested_evidence_allowed": False,
    },
    "formal_verification": {
        "esso_model_path": "src/kernels/dex/microkernel_composition_v2.yaml",
        "esso_status": "REQUIRED_NOT_IMPLEMENTED",
        "esso_solvers": ["Z3", "CVC5"],
        "esso_agreement_required": True,
        "esso_unknown_timeout_disagreement_policy": "REJECT",
        "port_implication_query": "PRODUCER_GUARANTEE_AND_NOT_CONSUMER_ASSUMPTION",
        "port_implication_expected_result": "UNSAT_BOTH_SOLVERS",
        "lean_theorem_path": "lean-mathlib/Proofs/ZenoDEXMicrokernelCompositionV2.lean",
        "lean_status": "REQUIRED_NOT_IMPLEMENTED",
    },
    "effects": {
        "committed_outbox_ancestor_required": True,
        "dispatch_stage": "AFTER_HEAD_COMMIT",
        "acknowledgment_stage": "SUBSEQUENT_CORE_COMMAND",
        "ack_command_id": "tau_withdrawal_ack",
        "ack_reentry_port_id": "P_SETTLEMENT_EXECUTION",
        "ack_occurrence_binding_fields": [
            "DESTINATION_ID",
            "OUTBOX_ID",
            "PAYLOAD_ROOT",
            "PROMOTION_SUBJECT_ROOT",
            "PUBLICATION_ROOT",
            "WRITER_EPOCH",
        ],
        "outbox_shell_economic_mutation_allowed": False,
        "idempotency_fields": [
            "DESTINATION_ID",
            "OUTBOX_ID",
            "PAYLOAD_ROOT",
            "PROMOTION_SUBJECT_ROOT",
            "PUBLICATION_ROOT",
            "WRITER_EPOCH",
        ],
    },
    "zrpf_admission_contract": {
        "ingress_port_id": "P_ZRPF_ROOT_INGRESS",
        "verification_port_id": "P_ZRPF_PROOF_VERIFICATION",
        "journal_type": "ZRPFRootJournalV2",
        "verified_witness_type": "VerifiedZRPFJournalV2",
        "execution_admission_type": "ExecutionAdmissionV2",
        "release_selected_image_required": True,
        "exact_journal_bytes_required": True,
        "opaque_witness_constructor": "RISC0_VERIFIER_ONLY",
        "current_head_recheck_required": True,
        "shared_transition_core_id": "ZENODEX_TRANSITION_CORE_V2",
        "publication_port_id": "P_SETTLEMENT_PUBLICATION",
        "commit_capability": "ZENO_LEDGER_SUBMIT_V2",
        "separate_zrpf_writer_allowed": False,
        "witness_candidate_equality_fields": sorted(REQUIRED_ZRPF_ADMISSION_BINDING_FIELDS),
        "binding_schema_paths": {
            token: list(paths)
            for token, paths in sorted(EXPECTED_ZRPF_BINDING_SCHEMA_PATHS.items())
        },
    },
    "candidate_publication_contract": {
        "execution_admission_constructor": "SETTLEMENT_KERNEL_ONLY",
        "execution_admission_required": True,
        "candidate_contains_admission_once": True,
        "publication_embeds_candidate_once": True,
        "duplicated_history_nullifier_proof_effect_fields": False,
        "value_delta_certificate_root_equals_commitment": True,
        "candidate_root_recomputed_by_writer": True,
        "publication_port_id": "P_SETTLEMENT_PUBLICATION",
    },
    "direct_core_id": "ZENODEX_TRANSITION_CORE_V2",
    "zrpf_core_id": "ZENODEX_TRANSITION_CORE_V2",
    "mounted_writer_capabilities": ["ZENO_LEDGER_SUBMIT_V2"],
}

EXPECTED_NONCLAIMS: Final = (
    "The candidate binds its declared input sources under an explicit external verifier-bootstrap premise and does not select or freeze an architecture.",
    "The already-running checker and Python interpreter are an explicit trusted bootstrap premise; an external authenticated executable-identity receipt is required and absent.",
    "Exact token-set checks are structural grade-2 evidence and do not prove semantic implication.",
    "ESSO Z3/CVC5 composition models and receipts are required and have not been implemented.",
    "The Lean global fold and refinement theorem is required and has not been implemented.",
    "No module, route, migration, verifier, proof guest, writer, or outbox adapter is implemented by this artifact.",
    "Boundary field names, logical types, units, and cardinalities are exact; command payload, domain-object, and delta-entry schemas remain open.",
    "The route intent shapes are proposed interface obligations and do not select open economic parameters.",
    "No settlement, mounting, release, migration, deployment, or production authority is granted.",
)

EXPECTED_TASK_GRAPH_SUMMARY: Final = (
    "The detailed V2 candidate structurally binds 33 routes, 20 modules, 13 state domains, "
    "25 typed ports, 56 module/intent asset-and-account capability rows, command-first and "
    "step-local intent composition, separate Tau connectivity/policy/release/governance "
    "authority, typed direct/ZRPF admission through one ZenoLedger writer, and 54 named "
    "mutants. The 33 command payload schemas and nested domain/delta schemas remain open; "
    "ESSO Z3/CVC5, Lean, runtime, migration, verifier-registry, no-bypass, and direct/ZRPF "
    "evidence remain open."
)

ROOT_KEYS: Final = frozenset(
    {
        "schema",
        "status",
        "production_promotion",
        "architecture_selected",
        "reviewed_subject",
        "parent_tournament",
        "source_pins",
        "verifier_bootstrap",
        "command_registry",
        "command_payload_schemas",
        "intent_registry",
        "intent_payload_schemas",
        "intent_capabilities",
        "view_registry",
        "route_constraint_registry",
        "type_registry",
        "state_domains",
        "module_descriptors",
        "port_contracts",
        "routes",
        "composition_contract",
        "evidence_gates",
        "named_mutants",
        "nonclaims",
    }
)
