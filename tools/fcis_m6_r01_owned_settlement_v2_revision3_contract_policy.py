"""Frozen policy constants for the M6-R01 OwnedSettlementV2 Revision 3 gate."""

from __future__ import annotations

SCHEMA = "zenodex/fcis/m6-r01-owned-settlement-v2-revision3-atdd/v1"

ROOT_FIELDS = {
    "acceptance_cases",
    "claim_cardinality_policy",
    "contract_version",
    "currentness_policy",
    "decision",
    "dependency_graph",
    "implementation_authorized",
    "mount_authorized",
    "no_authority_outputs",
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

REPLAY_PROJECTION_FIELDS = [
    "module",
    "version",
    "batch_ref",
    "included_intents",
    "fills",
    "balance_deltas",
    "reserve_deltas",
    "lp_deltas",
    "events",
]

REPLAY_PROJECTION_FORBIDDEN_FIELDS = [
    "provisional_protocol_fee_witnesses",
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

CONTROLLED_OCCURRENCE_FIELDS = [
    "exact_claim",
    "occurrence_id",
]

CONTROLLED_BATCH_FIELDS = [
    "exact_authenticated_command",
    "exact_pre_state",
    "state_bound_active_configuration",
    "authenticated_execution_context",
    "exact_owned_settlement",
    "exact_intent_tuple",
    "exact_controlled_occurrence_tuple",
]

FORBIDDEN_CONTROLLED_BATCH_FIELDS = [
    "exact_settlement_replay_projection",
    "exact_controlled_claim_tuple",
    "exact_occurrence_id_tuple",
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

NONINTERFERENCE_LAWS = [
    "projection_excludes_submitted_local_claim_tuple",
    "projection_components_are_recursively_closed_claim_independent_types",
    "recomputed_claim_predecessors_are_exact_and_claim_erased",
    "equal_projection_and_independent_sources_imply_equal_recomputed_claims",
    "claim_only_mutation_preserves_projection_and_recomputed_claims",
    "whole_claim_bearing_settlement_and_command_are_not_replay_inputs",
]

OCCURRENCE_PAIRING_LAWS = [
    "pair_count_equals_controlled_claim_count",
    "pair_i_claim_equals_controlled_claim_i",
    "pair_i_id_hashes_command_root_and_claim_i_settlement_fill_ordinal",
    "pair_order_equals_controlled_claim_order",
    "occurrence_ids_are_unique",
    "occurrence_ids_are_derived_and_never_caller_supplied",
    "normal_form_lineage_commits_every_ordered_occurrence_id",
    "equal_claims_under_distinct_command_roots_have_distinct_lineage",
]

RECOMPUTED_CLAIM_PREDECESSORS = [
    "exact_settlement_replay_projection_v2",
    "admitted_intent_tuple_v2",
    "exact_pre_state_v2",
    "state_bound_active_configuration_v2",
    "authenticated_execution_context_v2",
]

DOWNSTREAM_OCCURRENCE_SOURCE = (
    "state_bound_witness_batch_v2.exact_controlled_occurrence_tuple"
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

CURRENTNESS_POLICY = {
    "binder_establishes": "configuration_binding_to_one_exact_state_candidate",
    "binder_does_not_establish": "datastore_currentness",
    "historical_state_status": "candidate_evidence_only",
    "publication_requirement": (
        "atomically_load_store_current_exact_state_and_rederive_complete_batch"
    ),
}

NO_AUTHORITY_OUTPUTS = [
    "state_bound_active_configuration",
    "replay_candidate",
    "controlled_claim_tuple",
    "controlled_occurrence_tuple",
    "occurrence_id",
    "witness_batch",
    "batch_owned_controlled_occurrence_tuple",
    "v2_occurrence_normal_form",
    "successor",
    "patch",
    "allocation",
    "receipt",
    "bundle",
    "proof_input",
    "effect",
    "outbox",
]

REQUIRED_CASE_IDS = {
    f"ATDD-M6-R01-OSV2-R3-{index:03d}" for index in range(1, 15)
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

SOURCE_ROLE_FIELDS = {
    "authenticated_command_bytes",
    "authenticated_execution_context_v2",
    "downstream_occurrence_consumption",
    "exact_pre_state_v2",
    "exact_settlement_replay_projection_v2",
    "state_bound_active_configuration_v2",
    "submitted_claims",
    "submitted_roots",
    "validated_active_configuration_claim_v2",
}

NORMATIVE_SOURCE_FIELDS = {
    "architecture_path",
    "architecture_sha256",
    "current_command_root_path",
    "current_command_root_sha256",
    "implementation_base_commit",
    "provisional_fee_replay_path",
    "provisional_fee_replay_sha256",
    "provisional_fee_replay_values_path",
    "provisional_fee_replay_values_sha256",
    "revision_2_contract_path",
    "revision_2_contract_sha256",
    "revision_2_matrix_path",
    "revision_2_matrix_sha256",
    "revision_2_packet_commit",
    "revision_2_target_commit",
    "state_binding_path",
    "state_binding_sha256",
}

NORMATIVE_SOURCE = {
    "architecture_path": "docs/research/prompts/fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/SRGD_V1_AMENDMENT.md",
    "architecture_sha256": "c8fc946d916923fed8282112a5b4722fae774c67147e37a76b6099701f3f17e8",
    "current_command_root_path": "src/core/fcis_support_profile_v5.py",
    "current_command_root_sha256": "d6b10072761318b07813bb6b0898e7f5b6592b1cd22ef4ae7bf2d11073952000",
    "implementation_base_commit": "f891607a77671403042b34d6bc45d907aae69115",
    "provisional_fee_replay_path": "src/core/fcis_provisional_fee_replay_v2.py",
    "provisional_fee_replay_sha256": "2b91fa0f4835bc53d98a2b17ef3f08a659b4f7b52917dc353e15398fed285f9e",
    "provisional_fee_replay_values_path": "src/core/fcis_provisional_fee_replay_values_v2.py",
    "provisional_fee_replay_values_sha256": "f1bab3b7b6a2c56c2e3ad175cc1ead8f94b559370c120ad3c5cbe448863b9176",
    "revision_2_contract_path": "docs/research/FCIS_M6_R01_OWNED_SETTLEMENT_V2_WITNESS_LANGUAGE_REVISION_2_20260731.md",
    "revision_2_contract_sha256": "08dd04ad505913da7572a9437164f031f4935075ab5841bdc6bde8a63758aaef",
    "revision_2_matrix_path": "docs/research/FCIS_M6_R01_OWNED_SETTLEMENT_V2_ATDD_MATRIX_REVISION_2_20260731.json",
    "revision_2_matrix_sha256": "1de4c7af8b0b443151e60ede79ca8c94f74a8fee3530084465c160bb1278669a",
    "revision_2_packet_commit": "d6cd7e02e04b4721d993056bb95d68ab0dac1db9",
    "revision_2_target_commit": "16db3da7e3a6ee2716fac260f3de21b47bfd4827",
    "state_binding_path": "docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md",
    "state_binding_sha256": "cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5",
}

SOURCE_ROLES = {
    "authenticated_command_bytes": "freshly reauthenticated bytes used for extraction and command identity only",
    "authenticated_execution_context_v2": "independently authenticated execution context",
    "downstream_occurrence_consumption": "only the exact paired tuple nested in the controlled witness batch",
    "exact_pre_state_v2": "exact candidate state; store currentness exists only inside later publication",
    "exact_settlement_replay_projection_v2": "non-authoritative claim-erased view with no independent root",
    "state_bound_active_configuration_v2": "fresh binder output for the same exact state candidate used by replay",
    "submitted_claims": "equality targets only and never replay inputs",
    "submitted_roots": "equality targets only",
    "validated_active_configuration_claim_v2": "B1A-valid content with no state authority before binding",
}

NONCLAIMS = [
    "Revision 3 implements no OwnedSettlementV2 carrier or canonical codec.",
    "The claim-erased replay projection and noninterference relation are not implemented.",
    "The state-bound configuration, paired occurrences, and witness batch are not implemented.",
    "The current V1 SLNF adapter is not a conforming V2 paired-occurrence consumer.",
    "An exact-state binder does not prove datastore currentness.",
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
    "exact_settlement_replay_projection_v2",
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
    "exact_controlled_occurrence_tuple_v2",
    "state_bound_witness_batch_v2",
    "witness_batch_root_v2",
    "batch_owned_controlled_occurrence_tuple_v2",
    "v2_occurrence_normal_form_v2",
}

REQUIRED_EDGES = {
    ("authenticated_command_bytes", "exact_authenticated_command_v2"),
    ("exact_authenticated_command_v2", "admitted_owned_settlement_v2"),
    ("exact_authenticated_command_v2", "admitted_intent_tuple_v2"),
    ("exact_authenticated_command_v2", "command_root_v2"),
    ("exact_authenticated_command_v2", "state_bound_witness_batch_v2"),
    ("admitted_owned_settlement_v2", "admitted_local_claim_tuple_v2"),
    ("admitted_owned_settlement_v2", "exact_settlement_replay_projection_v2"),
    ("admitted_owned_settlement_v2", "owned_settlement_root_v2"),
    ("admitted_owned_settlement_v2", "command_root_v2"),
    ("admitted_owned_settlement_v2", "state_bound_witness_batch_v2"),
    ("admitted_intent_tuple_v2", "recomputed_local_claim_tuple_v2"),
    ("admitted_intent_tuple_v2", "command_root_v2"),
    ("admitted_intent_tuple_v2", "state_bound_witness_batch_v2"),
    ("admitted_local_claim_tuple_v2", "owned_settlement_root_v2"),
    ("admitted_local_claim_tuple_v2", "command_root_v2"),
    ("admitted_local_claim_tuple_v2", "exact_controlled_claim_tuple_v2"),
    ("exact_settlement_replay_projection_v2", "recomputed_local_claim_tuple_v2"),
    ("exact_pre_state_v2", "pre_state_root_v2"),
    ("exact_pre_state_v2", "state_bound_active_configuration_v2"),
    ("exact_pre_state_v2", "recomputed_local_claim_tuple_v2"),
    ("exact_pre_state_v2", "state_bound_witness_batch_v2"),
    ("validated_active_configuration_claim_v2", "state_bound_active_configuration_v2"),
    ("state_bound_active_configuration_v2", "configuration_root_v2"),
    ("state_bound_active_configuration_v2", "recomputed_local_claim_tuple_v2"),
    ("state_bound_active_configuration_v2", "state_bound_witness_batch_v2"),
    ("authenticated_execution_context_v2", "execution_context_hash_v2"),
    ("authenticated_execution_context_v2", "recomputed_local_claim_tuple_v2"),
    ("authenticated_execution_context_v2", "state_bound_witness_batch_v2"),
    ("recomputed_local_claim_tuple_v2", "exact_controlled_claim_tuple_v2"),
    ("exact_controlled_claim_tuple_v2", "exact_controlled_occurrence_tuple_v2"),
    ("command_root_v2", "exact_controlled_occurrence_tuple_v2"),
    ("exact_controlled_occurrence_tuple_v2", "state_bound_witness_batch_v2"),
    ("state_bound_witness_batch_v2", "witness_batch_root_v2"),
    ("state_bound_witness_batch_v2", "batch_owned_controlled_occurrence_tuple_v2"),
    ("batch_owned_controlled_occurrence_tuple_v2", "v2_occurrence_normal_form_v2"),
}

FORBIDDEN_EDGES = {
    ("exact_authenticated_command_v2", "recomputed_local_claim_tuple_v2"),
    ("admitted_owned_settlement_v2", "recomputed_local_claim_tuple_v2"),
    ("admitted_local_claim_tuple_v2", "recomputed_local_claim_tuple_v2"),
    ("owned_settlement_root_v2", "admitted_owned_settlement_v2"),
    ("command_root_v2", "admitted_owned_settlement_v2"),
    ("exact_controlled_occurrence_tuple_v2", "admitted_owned_settlement_v2"),
    ("witness_batch_root_v2", "state_bound_witness_batch_v2"),
    ("v2_occurrence_normal_form_v2", "state_bound_witness_batch_v2"),
}

EXACT_PREDECESSORS = {
    "recomputed_local_claim_tuple_v2": set(RECOMPUTED_CLAIM_PREDECESSORS),
    "state_bound_active_configuration_v2": {
        "exact_pre_state_v2",
        "validated_active_configuration_claim_v2",
    },
    "exact_controlled_occurrence_tuple_v2": {
        "exact_controlled_claim_tuple_v2",
        "command_root_v2",
    },
    "state_bound_witness_batch_v2": {
        "exact_authenticated_command_v2",
        "admitted_owned_settlement_v2",
        "admitted_intent_tuple_v2",
        "exact_pre_state_v2",
        "state_bound_active_configuration_v2",
        "authenticated_execution_context_v2",
        "exact_controlled_occurrence_tuple_v2",
    },
    "v2_occurrence_normal_form_v2": {
        "batch_owned_controlled_occurrence_tuple_v2",
    },
}
