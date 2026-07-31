"""Frozen policy constants for the M6-R01 OwnedSettlementV2 design gate."""

from __future__ import annotations

SCHEMA = "zenodex/fcis/m6-r01-owned-settlement-v2-atdd/v1"
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
    "fill_position",
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
REQUIRED_CASE_IDS = {
    f"ATDD-M6-R01-OSV2-{index:03d}" for index in range(1, 9)
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
    "exact_pre_state_v2",
    "submitted_roots",
    "validated_active_configuration_v2",
}
NORMATIVE_SOURCE_FIELDS = {
    "architecture_path",
    "architecture_sha256",
    "current_command_root_path",
    "current_command_root_sha256",
    "implementation_base_commit",
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
}
SOURCE_ROLES = {
    "authenticated_command_bytes": "freshly reauthenticated canonical command bytes",
    "authenticated_execution_context_v2": (
        "independently authenticated execution context"
    ),
    "exact_pre_state_v2": "store-current exact pre-state at publication",
    "submitted_roots": "equality targets only",
    "validated_active_configuration_v2": (
        "point-of-use B1A-validated active configuration bound to exact state"
    ),
}
NONCLAIMS = [
    "OwnedSettlementV2 admission and canonical codecs are not implemented.",
    "The controlled witness batch is not implemented.",
    "The command schema and root preimage are not frozen.",
    (
        "No state, configuration, receipt, bundle, proof, publication, "
        "or mount authority exists."
    ),
    "Python and Rust parity is not established.",
]
REQUIRED_EDGES = {
    ("authenticated_command_bytes", "admitted_owned_settlement_v2"),
    ("authenticated_command_bytes", "admitted_intent_tuple_v2"),
    ("authenticated_command_bytes", "command_root_v2"),
    ("authenticated_command_bytes", "state_bound_witness_batch_v2"),
    ("admitted_owned_settlement_v2", "admitted_local_claim_tuple_v2"),
    ("admitted_owned_settlement_v2", "owned_settlement_root_v2"),
    ("admitted_owned_settlement_v2", "command_root_v2"),
    ("admitted_owned_settlement_v2", "state_bound_witness_batch_v2"),
    ("admitted_intent_tuple_v2", "recomputed_local_claim_tuple_v2"),
    ("admitted_intent_tuple_v2", "command_root_v2"),
    ("admitted_intent_tuple_v2", "state_bound_witness_batch_v2"),
    ("admitted_local_claim_tuple_v2", "owned_settlement_root_v2"),
    ("exact_pre_state_v2", "pre_state_root_v2"),
    ("exact_pre_state_v2", "recomputed_local_claim_tuple_v2"),
    ("exact_pre_state_v2", "state_bound_witness_batch_v2"),
    ("validated_active_configuration_v2", "configuration_root_v2"),
    ("validated_active_configuration_v2", "recomputed_local_claim_tuple_v2"),
    ("validated_active_configuration_v2", "state_bound_witness_batch_v2"),
    ("authenticated_execution_context_v2", "execution_context_hash_v2"),
    ("authenticated_execution_context_v2", "recomputed_local_claim_tuple_v2"),
    ("authenticated_execution_context_v2", "state_bound_witness_batch_v2"),
    ("admitted_local_claim_tuple_v2", "exact_claim_tuple_equality_v2"),
    ("recomputed_local_claim_tuple_v2", "exact_claim_tuple_equality_v2"),
    ("recomputed_local_claim_tuple_v2", "state_bound_witness_batch_v2"),
    ("command_root_v2", "occurrence_id_tuple_v2"),
    ("exact_claim_tuple_equality_v2", "occurrence_id_tuple_v2"),
    ("owned_settlement_root_v2", "state_bound_witness_batch_v2"),
    ("command_root_v2", "state_bound_witness_batch_v2"),
    ("pre_state_root_v2", "state_bound_witness_batch_v2"),
    ("configuration_root_v2", "state_bound_witness_batch_v2"),
    ("execution_context_hash_v2", "state_bound_witness_batch_v2"),
    ("exact_claim_tuple_equality_v2", "state_bound_witness_batch_v2"),
    ("occurrence_id_tuple_v2", "state_bound_witness_batch_v2"),
    ("state_bound_witness_batch_v2", "witness_batch_root_v2"),
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
}
