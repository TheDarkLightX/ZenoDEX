"""Frozen policy constants for the M6-R01 OwnedSettlementV2 Revision 2 gate."""

from __future__ import annotations

SCHEMA = "zenodex/fcis/m6-r01-owned-settlement-v2-revision2-atdd/v1"

ROOT_FIELDS = {
    "acceptance_cases",
    "claim_cardinality_policy",
    "contract_version",
    "decision",
    "dependency_graph",
    "implementation_authorized",
    "mount_authorized",
    "no_successor_outputs",
    "nonclaims",
    "normative_source",
    "schema",
    "source_roles",
    "status",
}

OUTER_FIELDS = [
    "module",
    "version",
    "batch_ref",
    "included_intents",
    "fills",
    "balance_deltas",
    "reserve_deltas",
    "lp_deltas",
    "provisional_protocol_fee_witnesses",
    "events",
]

INNER_FIELDS = [
    "settlement_fill_ordinal",
    "intent_id",
    "fee_distribution_domain_id",
    "pool_snapshot_fingerprint",
    "pool_id",
    "asset",
    "sender_pubkey",
    "swap_kind",
    "recipient_pubkey",
    "asset_out",
    "amount_specified",
    "limit_amount",
    "recipient_output_credit",
    "total_fee_amount",
    "protocol_fee_share_bps",
    "sender_input_debit",
    "pool_reserve_credit",
    "provisional_fee_amount",
    "reserve_in_before",
    "reserve_out_before",
    "reserve_in_after",
    "reserve_out_after",
]

FORBIDDEN_INNER_FIELDS = [
    "fill_position",
    "claim_position",
    "command_root",
    "owned_settlement_root",
    "pre_state_root",
    "configuration_root",
    "execution_context_hash",
    "occurrence_id",
    "source_witness_root",
    "witness_batch_root",
    "receipt_root",
    "bundle_root",
    "outbox_root",
]

CONTROLLED_BATCH_FIELDS = [
    "exact_authenticated_command",
    "exact_pre_state",
    "state_bound_active_configuration",
    "authenticated_execution_context",
    "exact_owned_settlement",
    "exact_intent_tuple",
    "exact_controlled_claim_tuple",
    "exact_occurrence_id_tuple",
]

FORBIDDEN_CONTROLLED_BATCH_FIELDS = [
    "command_root",
    "pre_state_root",
    "configuration_root",
    "configuration_version",
    "algorithm_version",
    "accepted_language_version",
    "execution_context_hash",
    "owned_settlement_root",
    "witness_batch_root",
]

STATE_BINDING_LAWS = [
    "validated_root_equals_recomputed_body_root",
    "validated_root_equals_exact_pre_state_header_configuration_root",
    "validated_deployment_equals_exact_pre_state_header_deployment",
    "validated_activation_sequence_lte_exact_pre_state_header_sequence",
]

DOWNSTREAM_CLAIM_SOURCE = (
    "state_bound_witness_batch_v2.exact_controlled_claim_tuple"
)

CLAIM_CARDINALITY_POLICY = {
    "downstream_reenumeration_allowed": False,
    "empty_tuple_allowed": True,
    "occurrence_id_ordinal_source": "settlement_fill_ordinal",
    "ordinal_contiguous": False,
    "ordinal_field": "settlement_fill_ordinal",
    "ordinal_lower_bound": 0,
    "ordinal_order": "strictly_increasing",
    "ordinal_upper_bound_source": "len(exact_owned_settlement_v2.fills)",
    "positive_fee_emits_exactly_one_claim": True,
    "zero_fee_emits_claim": False,
}

REQUIRED_CASE_IDS = {
    f"ATDD-M6-R01-OSV2-R2-{index:03d}" for index in range(1, 13)
}

CASE_FIELDS = {
    "counterexample",
    "given",
    "id",
    "invariant",
    "nonclaims",
    "status",
    "then",
    "title",
    "when",
}

NO_SUCCESSOR_OUTPUTS = [
    "replay_candidate",
    "controlled_claim_tuple",
    "occurrence_id_tuple",
    "witness_batch",
    "successor",
    "patch",
    "allocation",
    "receipt",
    "bundle",
    "proof_input",
    "effect",
    "outbox",
]

SOURCE_ROLE_FIELDS = {
    "authenticated_command_bytes",
    "authenticated_execution_context_v2",
    "downstream_claim_consumption",
    "exact_pre_state_v2",
    "state_bound_active_configuration_v2",
    "submitted_roots",
    "validated_active_configuration_claim_v2",
}

NORMATIVE_SOURCE_FIELDS = {
    "architecture_path",
    "architecture_sha256",
    "current_command_root_path",
    "current_command_root_sha256",
    "implementation_base_commit",
    "revision_1_packet_commit",
    "revision_1_target_commit",
    "state_binding_path",
    "state_binding_sha256",
}

NORMATIVE_SOURCE = {
    "architecture_path": (
        "docs/research/prompts/"
        "fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/"
        "SRGD_V1_AMENDMENT.md"
    ),
    "architecture_sha256": (
        "c8fc946d916923fed8282112a5b4722fae774c67147e37a76b6099701f3f17e8"
    ),
    "current_command_root_path": "src/core/fcis_support_profile_v5.py",
    "current_command_root_sha256": (
        "d6b10072761318b07813bb6b0898e7f5b6592b1cd22ef4ae7bf2d11073952000"
    ),
    "implementation_base_commit": "f891607a77671403042b34d6bc45d907aae69115",
    "revision_1_packet_commit": "53beba00217274ec9357c3cf42fd11fa2501d306",
    "revision_1_target_commit": "dd4175ba5649e0c66d9c4af0594e747de8c3eea8",
    "state_binding_path": (
        "docs/research/"
        "FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_"
        "20260729.md"
    ),
    "state_binding_sha256": (
        "cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5"
    ),
}

SOURCE_ROLES = {
    "authenticated_command_bytes": (
        "freshly reauthenticated canonical command bytes"
    ),
    "authenticated_execution_context_v2": (
        "independently authenticated execution context"
    ),
    "downstream_claim_consumption": (
        "only the exact tuple nested in the controlled witness batch"
    ),
    "exact_pre_state_v2": "store-current exact pre-state at publication",
    "state_bound_active_configuration_v2": (
        "fresh binder output from the exact pre-state and B1A-validated claim"
    ),
    "submitted_roots": "equality targets only",
    "validated_active_configuration_claim_v2": (
        "B1A-valid content with no state authority before binding"
    ),
}

NONCLAIMS = [
    "Revision 2 implements no OwnedSettlementV2 carrier or canonical codec.",
    "The state-bound active configuration and controlled witness batch are not implemented.",
    "The current V1 SLNF adapter is not a conforming V2 sparse-ordinal consumer.",
    "The exact V2 command schema and root preimage are not frozen.",
    (
        "No state, configuration, transition, receipt, bundle, proof, "
        "publication, datastore, or mount authority exists."
    ),
    "Python and Rust parity is not established.",
]

REQUIRED_NODES = {
    "authenticated_command_bytes",
    "exact_authenticated_command_v2",
    "admitted_owned_settlement_v2",
    "admitted_intent_tuple_v2",
    "admitted_local_claim_tuple_v2",
    "exact_pre_state_v2",
    "validated_active_configuration_claim_v2",
    "state_bound_active_configuration_v2",
    "authenticated_execution_context_v2",
    "recomputed_local_claim_tuple_v2",
    "exact_controlled_claim_tuple_v2",
    "owned_settlement_root_v2",
    "command_root_v2",
    "pre_state_root_v2",
    "configuration_root_v2",
    "execution_context_hash_v2",
    "occurrence_id_tuple_v2",
    "state_bound_witness_batch_v2",
    "witness_batch_root_v2",
    "batch_owned_claim_tuple_v2",
    "v2_occurrence_normal_form_v2",
}

REQUIRED_EDGES = {
    ("authenticated_command_bytes", "exact_authenticated_command_v2"),
    ("exact_authenticated_command_v2", "admitted_owned_settlement_v2"),
    ("exact_authenticated_command_v2", "admitted_intent_tuple_v2"),
    ("exact_authenticated_command_v2", "command_root_v2"),
    ("exact_authenticated_command_v2", "recomputed_local_claim_tuple_v2"),
    ("exact_authenticated_command_v2", "state_bound_witness_batch_v2"),
    ("admitted_owned_settlement_v2", "admitted_local_claim_tuple_v2"),
    ("admitted_owned_settlement_v2", "owned_settlement_root_v2"),
    ("admitted_owned_settlement_v2", "command_root_v2"),
    ("admitted_owned_settlement_v2", "recomputed_local_claim_tuple_v2"),
    ("admitted_owned_settlement_v2", "state_bound_witness_batch_v2"),
    ("admitted_intent_tuple_v2", "recomputed_local_claim_tuple_v2"),
    ("admitted_intent_tuple_v2", "command_root_v2"),
    ("admitted_intent_tuple_v2", "state_bound_witness_batch_v2"),
    ("admitted_local_claim_tuple_v2", "owned_settlement_root_v2"),
    ("admitted_local_claim_tuple_v2", "exact_controlled_claim_tuple_v2"),
    ("exact_pre_state_v2", "pre_state_root_v2"),
    ("exact_pre_state_v2", "state_bound_active_configuration_v2"),
    ("exact_pre_state_v2", "recomputed_local_claim_tuple_v2"),
    ("exact_pre_state_v2", "state_bound_witness_batch_v2"),
    (
        "validated_active_configuration_claim_v2",
        "state_bound_active_configuration_v2",
    ),
    ("state_bound_active_configuration_v2", "configuration_root_v2"),
    (
        "state_bound_active_configuration_v2",
        "recomputed_local_claim_tuple_v2",
    ),
    (
        "state_bound_active_configuration_v2",
        "state_bound_witness_batch_v2",
    ),
    ("authenticated_execution_context_v2", "execution_context_hash_v2"),
    (
        "authenticated_execution_context_v2",
        "recomputed_local_claim_tuple_v2",
    ),
    (
        "authenticated_execution_context_v2",
        "state_bound_witness_batch_v2",
    ),
    ("recomputed_local_claim_tuple_v2", "exact_controlled_claim_tuple_v2"),
    ("exact_controlled_claim_tuple_v2", "occurrence_id_tuple_v2"),
    ("command_root_v2", "occurrence_id_tuple_v2"),
    ("exact_controlled_claim_tuple_v2", "state_bound_witness_batch_v2"),
    ("occurrence_id_tuple_v2", "state_bound_witness_batch_v2"),
    ("state_bound_witness_batch_v2", "witness_batch_root_v2"),
    ("state_bound_witness_batch_v2", "batch_owned_claim_tuple_v2"),
    ("batch_owned_claim_tuple_v2", "v2_occurrence_normal_form_v2"),
}

FORBIDDEN_BACK_EDGES = {
    ("owned_settlement_root_v2", "admitted_owned_settlement_v2"),
    ("owned_settlement_root_v2", "admitted_local_claim_tuple_v2"),
    ("command_root_v2", "admitted_owned_settlement_v2"),
    ("command_root_v2", "admitted_local_claim_tuple_v2"),
    ("occurrence_id_tuple_v2", "admitted_owned_settlement_v2"),
    ("occurrence_id_tuple_v2", "admitted_local_claim_tuple_v2"),
    ("witness_batch_root_v2", "admitted_owned_settlement_v2"),
    ("witness_batch_root_v2", "state_bound_witness_batch_v2"),
    ("v2_occurrence_normal_form_v2", "state_bound_witness_batch_v2"),
}
