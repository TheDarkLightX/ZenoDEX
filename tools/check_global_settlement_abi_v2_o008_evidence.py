"""Fail-closed checker for the bounded O-008 GlobalSettlementABI V2 packet.

This checker validates evidence shape and source binding only.  The closed
expected registries stay beside the validator so one review surface contains
the complete frozen contract.  A successful check grants no verifier,
settlement, publisher, release, or production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections.abc import Mapping
from functools import lru_cache
from pathlib import Path
from typing import Any, cast

SCHEMA = "zenodex/global-settlement-abi-v2/o008-bounded-core-evidence/v1"
REPORT_SCHEMA = f"{SCHEMA}/check-report/v1"
SUBJECT_COMMIT = "1a1edeb569dc71aedbe0ea75bdc61758e6f583cc"
REPO_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = (
    REPO_ROOT
    / "docs/research/GLOBAL_SETTLEMENT_ABI_V2_O008_BOUNDED_CORE_EVIDENCE_20260831.json"
)

EXPECTED_DEPENDENCIES = {
    "O-006": "OPEN_UNVERIFIED",
    "O-007C": "OPEN_UNVERIFIED",
    "O-008A": "OPEN_UNVERIFIED",
}

EXPECTED_NONCLAIMS = [
    "runtime_mounting",
    "risc0_guest_or_receipt",
    "tau_refinement",
    "publisher_authority",
    "settlement_authority",
    "release_or_profile_authentication",
    "migration_or_recovery_closure",
    "production_readiness",
    "whole_program_value_movement",
    "collection_bound_completeness",
]

EXPECTED_LANES = [
    "ASSET_TRANSFER",
    "SPOT_LIQUIDITY",
    "FARM_INCENTIVES",
    "ZDEX_TOKENOMICS",
    "ZUSD_MONETARY",
    "PERPS_MARKET",
    "ORACLE_MARKET",
    "SEALED_AUCTION",
    "STRATEGY_ESCROW",
    "PROOF_REWARDS",
    "EXTERNAL_CUSTODY",
    "GOVERNANCE_MIGRATION",
]

EXPECTED_LANE_SEMANTICS = {
    "ASSET_TRANSFER": "BOUNDED_PYTHON_ASSET_SLICE_WITH_RUST_TRANSFER_ONLY",
    "SPOT_LIQUIDITY": "SEMANTIC_GAP",
    "FARM_INCENTIVES": "SEMANTIC_GAP",
    "ZDEX_TOKENOMICS": "SEMANTIC_GAP",
    "ZUSD_MONETARY": "SEMANTIC_GAP",
    "PERPS_MARKET": "SEMANTIC_GAP",
    "ORACLE_MARKET": "GLOBAL_ORACLE_LIFECYCLE_RECONCILIATION_ONLY_NO_LANE_CORE",
    "SEALED_AUCTION": "SEMANTIC_GAP",
    "STRATEGY_ESCROW": "SEMANTIC_GAP",
    "PROOF_REWARDS": "SEMANTIC_GAP",
    "EXTERNAL_CUSTODY": "STRUCTURAL_ONLY_OUTBOX_CLOSED_PRE_O009",
    "GOVERNANCE_MIGRATION": "STRUCTURAL_ONLY_NO_MIGRATION_TRANSITION",
}

EXPECTED_ENUMS = {
    "LaneIdV2": EXPECTED_LANES,
    "EconomicEffectKindV2": ["ACCOUNT_MOVEMENT", "ISSUE", "BURN", "CUSTODY", "LIABILITY", "RESERVE", "FEE_ALLOCATION", "REWARD", "SLASH"],
    "TerminalObligationStatusV2": ["OPEN", "DRAINED", "TOMBSTONED"],
    "OutboxStatusV2": ["PENDING", "ACKNOWLEDGED"],
    "GlobalEconomicRefinementRejectCodeV2": [
        "MALFORMED_CANDIDATE", "EXTERNAL_OUTBOX_REQUIRES_PUBLISHER",
        "ZERO_OCCURRENCE_NOT_STATIC", "FIXED_CONTEXT_CHANGED",
        "LANE_OWNERSHIP_CHANGED", "DISABLED_LANE_WRITE",
        "LANE_WRITE_COVERAGE_MISMATCH", "LANE_WRITE_ROOT_MISMATCH",
        "SIGNED_STATE_DELTA_OVERFLOW", "BALANCES_STATE_EFFECT_MISMATCH",
        "CUSTODY_STATE_EFFECT_MISMATCH", "LIABILITIES_STATE_EFFECT_MISMATCH",
        "RESERVES_STATE_EFFECT_MISMATCH", "SUPPLY_EFFECT_TOTAL_OVERFLOW",
        "SUPPLY_ISSUE_BURN_MISMATCH", "OWNED_ACCOUNTING_TOTAL_OVERFLOW",
        "OWNED_TOTAL_NOT_SUPPLY", "CONSERVATION_ASSET_COVERAGE_MISMATCH",
        "CONSERVATION_STATE_MISMATCH", "ANNOTATION_MIRROR_OVERFLOW",
        "FEE_ALLOCATION_NOT_MIRRORED", "REWARD_OR_SLASH_NOT_MIRRORED",
        "ZERO_FEE_CONSERVATION_ROW", "FEE_RESIDUE_OVERFLOW",
        "FEE_RESIDUE_STATE_MISMATCH", "CUSTODY_BACKING_TOTAL_OVERFLOW",
        "LIABILITY_TOTAL_OVERFLOW", "LIABILITIES_EXCEED_BACKING",
        "OPEN_TERMINAL_TOTAL_OVERFLOW", "OPEN_TERMINAL_EXCEEDS_LIABILITY",
        "TERMINAL_LIABILITY_DELTA_OVERFLOW", "TERMINAL_PRE_STATE_MISMATCH",
        "TERMINAL_OWNING_LANE_WRITE_MISSING", "TERMINAL_PLAN_MISMATCH",
        "TERMINAL_LIABILITY_MISMATCH", "ORACLE_LANE_WRITE_MISSING",
        "ORACLE_PRE_STATE_MISMATCH", "ORACLE_PLAN_MISMATCH",
        "OCCURRENCES_NOT_ORDERED_UNIQUE", "REPLAY_CONSUMPTION_MISMATCH",
        "OCCURRENCE_CONTEXT_MISMATCH", "REPLAY_ALREADY_CONSUMED",
        "REPLAY_POST_STATE_MISMATCH", "HEIGHT_PROGRESSION_MISMATCH",
        "OCCURRENCE_HEIGHT_MISMATCH", "INTERNAL_CONTRACT_DRIFT",
    ],
    "AssetClassV2": [
        "tau_native_coin",
        "canonical_zusd",
        "lp_share",
        "zdex_protocol_token",
        "sealed_bid_payment_or_inventory",
        "registered_ordinary_token",
    ],
    "AssetTransferRejectCodeV2": [
        "MISSING_OCCURRENCE",
        "OCCURRENCE_BINDING_MISMATCH",
        "RELEASE_MISMATCH",
        "UNKNOWN_COMMAND",
        "OCCURRENCE_COMMAND_MISMATCH",
        "UNKNOWN_ASSET",
        "DISABLED_ASSET",
        "UNREGISTERED_ASSET",
        "ASSET_ORIGIN_MISMATCH",
        "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED",
        "UNAUTHORIZED_SUBJECT",
        "SELF_TRANSFER",
        "ZERO_AMOUNT",
        "FEE_LIMIT_EXCEEDED",
        "EFFECT_DELTA_OVERFLOW",
        "INSUFFICIENT_BALANCE",
        "BALANCE_OVERFLOW",
    ],
    "ManagedAssetLifecycleRejectCodeV2": [
        "MISSING_OCCURRENCE",
        "OCCURRENCE_BINDING_MISMATCH",
        "RELEASE_MISMATCH",
        "UNKNOWN_COMMAND",
        "OCCURRENCE_COMMAND_MISMATCH",
        "UNKNOWN_ASSET",
        "DISABLED_ASSET",
        "ASSET_CLASS_MISMATCH",
        "ASSET_DECIMALS_MISMATCH",
        "UNREGISTERED_ASSET",
        "ASSET_ORIGIN_MISMATCH",
        "GENERIC_AUTHORITY_FORBIDDEN",
        "ISSUE_DISABLED",
        "BURN_DISABLED",
        "UNAUTHORIZED_SUBJECT",
        "AUTHORIZATION_ROOT_MISMATCH",
        "ZERO_AMOUNT",
        "EFFECT_DELTA_OVERFLOW",
        "INSUFFICIENT_BALANCE",
        "BALANCE_OVERFLOW",
        "SUPPLY_OVERFLOW",
    ],
    "AssetLaneRouteV2": ["TRANSFER", "MANAGED_LIFECYCLE", "COORDINATOR"],
    "AssetLaneCoordinatorRejectCodeV2": [
        "REGISTRY_BINDING_MISMATCH",
        "CANDIDATE_BINDING_MISMATCH",
        "PROJECTION_MISMATCH",
    ],
    "AssetOriginKindV2": ["NATIVE", "TAU_ORIGINATED"],
    "AssetOriginRegistrationRejectCodeV2": [
        "MISSING_OCCURRENCE",
        "OCCURRENCE_BINDING_MISMATCH",
        "RELEASE_MISMATCH",
        "UNKNOWN_COMMAND",
        "OCCURRENCE_COMMAND_MISMATCH",
        "UNAUTHORIZED_SUBJECT",
        "GRANT_MISMATCH",
        "DECIMAL_SCALE_MISMATCH",
        "DISABLED_ORIGIN_KIND",
        "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED",
        "DUPLICATE_ASSET",
        "DUPLICATE_ORIGIN",
    ],
}

EXPECTED_PROJECTION_FIELD_ORDERS = {
    "EconomicAmountV2": ["owner", "asset", "custody_domain", "amount_atoms"],
    "AssetSupplyV2": ["asset", "amount_atoms"],
    "EconomicEffectRowV2": ["kind", "principal", "asset", "custody_domain", "delta_atoms"],
    "AssetConservationRowV2": ["asset", "owned_and_custodied_pre_atoms", "owned_and_custodied_post_atoms", "supply_pre_atoms", "supply_post_atoms", "authorized_issue_atoms", "authorized_burn_atoms"],
    "FeeConservationRowV2": ["asset", "fee_charged_atoms", "current_allocations_atoms", "carried_residue_atoms"],
    "LaneWriteV2": ["lane_id", "pre_root", "post_root"],
    "ExternalOutboxEnqueueV2": ["effect_id", "destination_id", "payload_hash", "adapter_profile_root"],
    "GlobalEconomicEffectPlanV2": ["schema", "rows", "asset_conservation", "fee_conservation", "lane_writes", "occurrence_consumptions", "external_outbox_enqueue"],
    "OracleOccurrenceStateV2": ["oracle_id", "occurrence_root", "observed_height", "finalized"],
    "OracleOccurrenceDeltaV2": ["oracle_id", "pre_occurrence", "post_occurrence"],
    "GlobalOracleOccurrencePlanV2": ["schema", "deltas"],
    "TerminalObligationV2": ["obligation_id", "lane_id", "claimant", "asset", "liability_domain", "amount_atoms", "status"],
    "TerminalObligationDeltaV2": ["obligation_id", "pre_obligation", "post_obligation"],
    "GlobalTerminalObligationPlanV2": ["schema", "deltas"],
    "EconomicCommandOccurrenceV2": ["schema", "chain_id", "deployment_root", "height", "tx_index", "op_index", "command_kind", "command_body_hash", "route_release_id", "subject_id", "grant_root", "nonce", "profile_root", "pre_state_root", "consumed_object_ids"],
    "LaneModuleTransitionJournalV2": ["schema", "chain_id", "deployment_root", "profile_root", "writer_epoch", "lane_id", "module_release_id", "command_occurrence_id", "pre_lane_root", "post_lane_root", "effect_plan_root", "private_port_root", "receipt_root", "terminal_obligations_root", "oracle_occurrence_plan_root"],
    "LaneStateRootV2": ["lane_id", "module_release_id", "enabled", "state_root"],
    "ReplayStateV2": ["replay_id", "occurrence_id"],
    "OutboxStateV2": ["effect_id", "destination_id", "payload_hash", "adapter_profile_root", "commit_id", "status"],
    "GlobalEconomicStateV2": ["schema", "chain_id", "deployment_root", "writer_epoch", "height", "profile_root", "lane_roots", "balances", "supplies", "custody", "liabilities", "reserves", "oracle_occurrences", "replay_state", "terminal_obligations", "history_root", "outbox"],
    "GlobalEconomicStateRootV2": ["root", "profile_root", "writer_epoch", "height"],
    "GlobalEconomicStateEffectRefinementCandidateV2": ["pre_state", "post_state", "effect_plan", "consumed_occurrences", "terminal_plan", "oracle_plan"],
    "GlobalEconomicStateEffectRefinementV2": ["pre_state_root", "post_state_root", "effect_plan_root", "terminal_plan_root", "oracle_plan_root", "state_delta_root", "production_authority", "refinement_root"],
    "GlobalEconomicRefinementAcceptedV2": ["witness", "production_authority"],
    "GlobalEconomicRefinementRejectedV2": ["reject_code", "pre_state_root", "post_state_root", "effect_plan", "terminal_plan", "oracle_plan", "consumed_occurrences", "outbox", "production_authority"],
    "AssetTransferPolicyV2": ["asset", "fee_owner", "transfer_fee_atoms", "enabled", "asset_class", "asset_origin_root", "atom_decimals"],
    "AssetTransferStateV2": ["schema", "module_release_id", "policies", "balances", "supplies"],
    "AssetTransferContextV2": ["writer_epoch", "module_release_id", "global_pre_state_root", "occurrence"],
    "AssetTransferCommandV2": ["command_kind", "asset", "sender", "recipient", "amount_atoms", "max_fee_atoms", "asset_origin_root"],
    "AssetTransferAcceptedV2": ["post_state", "effects", "module_journal", "production_authority"],
    "AssetTransferRejectedV2": ["code", "pre_state_root", "post_state_root", "effects"],
    "ManagedAssetLifecyclePolicyV2": ["asset", "asset_class", "asset_origin_root", "atom_decimals", "issue_authority_subject", "issue_authorization_root", "burn_authorization_root", "enabled"],
    "ManagedAssetLifecycleStateV2": ["schema", "module_release_id", "policies", "balances", "supplies"],
    "ManagedAssetLifecycleContextV2": ["writer_epoch", "module_release_id", "global_pre_state_root", "occurrence"],
    "ManagedAssetLifecycleCommandV2": ["command_kind", "asset", "asset_class", "asset_origin_root", "atom_decimals", "authorization_root", "account_owner", "amount_atoms"],
    "ManagedAssetLifecycleAcceptedV2": ["post_state", "effects", "module_journal", "receipt_root", "production_authority"],
    "ManagedAssetLifecycleRejectedV2": ["code", "pre_state_root", "post_state_root", "effects", "terminal_obligations_root", "oracle_occurrence_plan_root", "production_authority"],
    "AssetOriginRecordV2": ["asset", "origin_kind", "origin_root", "transfer_policy_root", "issue_policy_root", "decimals", "asset_class"],
    "AssetOriginRegistrationPolicyV2": ["authority_subject", "authority_grant_root", "allow_native", "allow_tau_originated"],
    "AssetOriginRegistryStateV2": ["schema", "module_release_id", "policy", "assets"],
    "AssetOriginRegistrationContextV2": ["writer_epoch", "module_release_id", "global_pre_state_root", "occurrence"],
    "AssetOriginRegistrationCommandV2": ["command_kind", "asset", "origin_kind", "origin_root", "transfer_policy_root", "issue_policy_root", "decimals", "asset_class"],
    "AssetOriginRegistrationAcceptedV2": ["post_state", "effects", "module_journal", "production_authority"],
    "AssetOriginRegistrationRejectedV2": ["code", "pre_state_root", "post_state_root", "effects"],
    "AssetLaneStateV2": ["schema", "module_release_id", "origin_registry", "transfer_policies", "managed_policies", "balances", "supplies"],
    "AssetLaneContextV2": ["writer_epoch", "module_release_id", "global_pre_state_root", "occurrence"],
    "AssetLaneAcceptedV2": ["route", "source_leaf_journal_root", "post_state", "effects", "module_journal", "receipt_root", "production_authority", "profile_authentication"],
    "AssetLaneRejectedV2": ["route", "code", "pre_state_root", "post_state_root", "effects", "production_authority", "profile_authentication"],
}

GAP_NO_CANONICAL_ENCODER = {
    "GlobalEconomicStateEffectRefinementCandidateV2",
    "GlobalEconomicStateEffectRefinementV2",
    "GlobalEconomicRefinementAcceptedV2",
    "GlobalEconomicRefinementRejectedV2",
    "ManagedAssetLifecycleAcceptedV2",
    "ManagedAssetLifecycleRejectedV2",
    "AssetOriginRegistrationAcceptedV2",
    "AssetOriginRegistrationRejectedV2",
    "AssetLaneContextV2",
    "AssetLaneAcceptedV2",
    "AssetLaneRejectedV2",
}

EXPECTED_FIELD_PROFILE_OVERRIDES = {
    ("TerminalObligationV2", "obligation_id"): "token",
    ("TerminalObligationDeltaV2", "obligation_id"): "token",
    ("EconomicCommandOccurrenceV2", "consumed_object_ids"): "ordered_tokens",
    ("LaneModuleTransitionJournalV2", "command_occurrence_id"): "root",
    ("LaneModuleTransitionJournalV2", "receipt_root"): "root",
    ("GlobalEconomicRefinementRejectedV2", "consumed_occurrences"): "ordered_records",
    ("GlobalEconomicRefinementRejectedV2", "production_authority"): "authority_none",
    ("AssetTransferPolicyV2", "asset_origin_root"): "optional_root",
    ("AssetTransferCommandV2", "asset_origin_root"): "optional_root",
    ("ManagedAssetLifecyclePolicyV2", "asset_origin_root"): "optional_root",
    ("ManagedAssetLifecycleCommandV2", "asset_origin_root"): "optional_root",
    ("ManagedAssetLifecycleCommandV2", "authorization_root"): "optional_root",
    ("AssetOriginRecordV2", "issue_policy_root"): "root_zero",
    ("AssetOriginRegistrationCommandV2", "issue_policy_root"): "root_zero",
    ("GlobalEconomicStateEffectRefinementV2", "terminal_plan_root"): "root_zero",
    ("GlobalEconomicStateEffectRefinementV2", "oracle_plan_root"): "root_zero",
    ("AssetLaneAcceptedV2", "profile_authentication"): "authentication_unverified",
    ("AssetLaneRejectedV2", "profile_authentication"): "authentication_unverified",
}

EXPECTED_COLLECTION_KEYS = {
    "EconomicEffectRowV2": ["kind", "asset", "principal", "custody_domain"],
    "EconomicCommandOccurrenceV2": ["derived:occurrence_id"],
}

EXPECTED_EQUATIONS = [
    "OWNED_DEFINITION",
    "OWNED_EQUALS_SUPPLY_PRE_POST",
    "ISSUE_BURN_CONSERVATION",
    "ISSUE_BURN_EFFECT_PROJECTION",
    "LIABILITY_BACKING",
    "CLAIMANT_TERMINAL_BOUND",
    "FEE_DECOMPOSITION",
    "FEE_RESIDUE_MIRROR",
    "FEE_ALLOCATION_POSITIVE_CREDIT",
    "ASSET_TRANSFER_LOCAL_CONSERVATION",
    "MANAGED_ISSUE_BURN_CONSERVATION",
]

EXPECTED_EQUATION_SOURCES = {
    "OWNED_DEFINITION": "src/core/global_economic_state_effect_refinement_v2.py",
    "OWNED_EQUALS_SUPPLY_PRE_POST": "src/core/global_economic_refinement_checks_v2.py",
    "ISSUE_BURN_CONSERVATION": "src/core/global_economic_refinement_checks_v2.py",
    "ISSUE_BURN_EFFECT_PROJECTION": "src/core/global_economic_refinement_checks_v2.py",
    "LIABILITY_BACKING": "src/core/global_economic_refinement_checks_v2.py",
    "CLAIMANT_TERMINAL_BOUND": "src/core/global_economic_refinement_checks_v2.py",
    "FEE_DECOMPOSITION": "src/core/global_economic_refinement_checks_v2.py",
    "FEE_RESIDUE_MIRROR": "src/core/global_economic_refinement_checks_v2.py",
    "FEE_ALLOCATION_POSITIVE_CREDIT": "src/core/global_economic_refinement_checks_v2.py",
    "ASSET_TRANSFER_LOCAL_CONSERVATION": "src/core/asset_transfer_module_v2.py",
    "MANAGED_ISSUE_BURN_CONSERVATION": "src/core/managed_asset_lifecycle_module_v2.py",
}

EXPECTED_FORMAL_THEOREMS = {
    "lean-mathlib/Proofs/GlobalSettlementCoreV2.lean": [
        "allLaneIds_complete",
        "negative_fee_allocation_rejected",
        "fee_projection_mismatch_rejected",
        "netOnlyMutation_projection_rejected",
    ],
    "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean": [
        "accepted_preserves_owned_supply",
        "accepted_preserves_liability_backing",
        "accepted_open_terminal_totals_fit_exact_liability_rows",
        "accepted_fee_credit_and_residue_are_exact",
        "accepted_has_exact_lane_write_coverage",
        "rejected_is_no_op_bundle",
    ],
    "lean-mathlib/Proofs/AssetTransferRefinementV2.lean": [
        "transition_total",
        "rejected_post_eq_pre",
        "rejected_effects_empty",
        "accepted_consumes_exact_occurrence",
        "accepted_conservation_row_exact",
        "fee_owner_sender_alias_is_locally_conserving",
        "omitted_fee_credit_breaks_conservation_counterexample",
    ],
    "lean-mathlib/Proofs/ManagedAssetLifecycleRefinementV2.lean": [
        "transition_total",
        "rejected_post_eq_pre",
        "rejected_effects_empty",
        "accepted_authorization_guard",
        "accepted_conservation_equations",
        "accepted_issue_authority_exact",
        "accepted_burn_authority_exact",
        "stateful_issue_transfer_burn_trace",
        "protocol_issue_rejects_generic_authority_counterexample",
    ],
}

EXPECTED_HASHES = {
    "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json": "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f",
    "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.md": "da42739f085b3344d4a1240ea0a77fa91b9def05c5c6a530dad7d789d2e920f6",
    "src/core/global_settlement_primitives_v2.py": "11a26694357812e91b398bddc2b6bbec0a93063731ccd5b23818de1d0c0ca01e",
    "src/core/global_settlement_effect_values_v2.py": "a366616f8a11f35d5c69d29c91e1d0b8598ac48499eb44d86d8011c73d30fb9a",
    "src/core/global_settlement_effect_plan_v2.py": "e352b67a13ac22e09d31d5aebf94d10aa7f540ef3149050ed2675854f6b839f0",
    "src/core/global_settlement_lifecycle_v2.py": "70e49b99a2ee617ef535beb577b975b302faea7aa14134de0791bd493e342471",
    "src/core/global_economic_proof_v2.py": "087b4df5295d82d112d552bac136b66cf0010f078915c29869d7a427fd8d5705",
    "src/core/global_economic_state_ownership_v2.py": "435ce66dd5233f4cb5d4553d106bd0347c3ccda82a98572080680663ecdaad8e",
    "src/core/global_economic_state_v2.py": "2948531057e332a301c0cdd278771040a86eda38f34ca839cd1ec196fc75b12e",
    "src/core/global_economic_refinement_checks_v2.py": "f8084730492024764f9f2f2008e4e04c7c7d28455358885bd4f6c758eb99f1c6",
    "src/core/global_economic_state_effect_refinement_v2.py": "4663cbee5ff7485b65bc68e55058bbe49cbc0ddd0c6e2f9c6b9502928c9713b7",
    "src/core/global_economic_refinement_outcome_v2.py": "a0d6b4d6c12f2da81300675f6b923926294bfeade3ddc4ee10bf1374ffef508e",
    "src/core/asset_transfer_types_v2.py": "345ddc4a414b8526d7e52e53b22cbc987bfa4b9ad3b2573d0aa5ae37c8f74283",
    "src/core/asset_transfer_module_v2.py": "df0a25077d508db805afa0b828edbe5c8becdd362401f778fef0ce1f8649d065",
    "src/core/managed_asset_lifecycle_state_v2.py": "cacb73ed865c35533377114d1eed9c01a630359fa435f2e64a416daec038c981",
    "src/core/managed_asset_lifecycle_result_v2.py": "d5f19e377fe721d3bcd7fd99732128c80e2839bffa5315c76fa07dca9e74e35a",
    "src/core/managed_asset_lifecycle_module_v2.py": "a7278af80244a51302670138e9f50876ba72db1246bd8b6f1af90ac65b595a48",
    "src/core/asset_origin_registry_types_v2.py": "9b1a0cdde0909dd1c1729804277b34805f4877e849a1e3e897540053643b23e4",
    "src/core/asset_origin_registry_v2.py": "30a94b99eda4c395b5510fb11bf295171399290f3db72112092a42eb00850be4",
    "src/core/asset_lane_state_v2.py": "ecbe37b11f5f80aaa0f114c3c5f08454a0e302f4b7830bbc55a894cbeb655034",
    "src/core/asset_lane_coordinator_values_v2.py": "e138c22f4fb85d85ba969e7f45ddc51b304ea5b11fb9ef4b866c282a8956efde",
    "src/core/asset_lane_coordinator_v2.py": "be82d0ad5a7bc5ed49305a44711de9ca53a21f4ac7fc69fd1f232b33bc9462f8",
    "zk/global_settlement_abi_v2/src/canonical.rs": "b17a76d6e8ce5915ba1d250982147dceda0d7368911b396f7ae83fd860216053",
    "zk/global_settlement_abi_v2/src/state.rs": "28c515697fe08190142f5885e60e7cfcf650cf472ab0f3535b34ed154a831846",
    "zk/global_settlement_abi_v2/src/effect_values.rs": "2546015b68ddf0197cdf584dcefde8a7d7ae0eb6d77e24f98ba86fb375400f24",
    "zk/global_settlement_abi_v2/src/effects.rs": "38f4be8275fdabed5b3af792dc9c16292a4ed6b2cd57ee1812afa881c301cf84",
    "zk/global_settlement_abi_v2/src/lifecycle.rs": "b0561bd8ca9943b3f096a402c0c993d65ac5d6207388b5b0480877a40cdd37f6",
    "zk/global_settlement_abi_v2/src/proof.rs": "f0fb984ae594284795c1c01a54a6e0dffacd69b4732a2fd7153128ce7a691dce",
    "zk/global_settlement_abi_v2/src/global_state.rs": "b007d8b7dad5136821fd000794bb3e6f3d8b952fbca6a5e1d8bfafa2375a6b92",
    "zk/global_settlement_abi_v2/src/global_refinement.rs": "f18d51eabad485f0d2c9a625ada7c573600076b314c10d992c68c7dd68702e31",
    "zk/global_settlement_abi_v2/src/global_refinement_checks.rs": "6b9e7c9e41b94dec1d9076205a5dcf0e76208b8d345c36a2890fe87921bf4259",
    "zk/global_settlement_abi_v2/src/global_refinement_annotations.rs": "dbb2aacc7af202bfeb41f9e0f9b3b88c605a18eb2d1314092172ee7016c649de",
    "zk/global_settlement_abi_v2/src/global_refinement_lifecycle.rs": "574214d8004ac5f4f80916ba3416e020b5afcbe4b1cd7cbd7345feb309027b0d",
    "zk/global_settlement_abi_v2/src/outcome.rs": "5973d04e50c951c6d98a1ad17f609c5fd2d3060657e6cb74726b4e9830467223",
    "zk/global_settlement_abi_v2/src/asset_transfer_types.rs": "599b478ff18e7270650eddd005c22c2124ceebbe137a029fb7b7fe6e51efe3c2",
    "zk/global_settlement_abi_v2/src/asset_transfer.rs": "a21aea1c2e642948edcdf7a0466b035bc26203572c5c22dc7185493e04077198",
    "zk/global_settlement_abi_v2/src/lib.rs": "f27b122cc5b55cffbeb646409f23fb2439d1a7bb2f908d5c57e84da472cfc97e",
    "lean-mathlib/Proofs/GlobalSettlementCoreV2.lean": "2ce254367dc8e8299f82f8a93e09c1d470f3a218ed01af7efb766946a34255a4",
    "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean": "85448be52a0ad003a953e12f46b558face3650282ac238c8ac7bb8a002a55867",
    "lean-mathlib/Proofs/AssetTransferRefinementV2.lean": "4401a6bb2718285768f510c91690bbff4d0928b05e2a57f6a8985379f5ff2772",
    "lean-mathlib/Proofs/ManagedAssetLifecycleRefinementV2.lean": "e3054b8d7580486dadc70ad36e6ac0e3a8b4435504779421081b475acbde2983",
    "tests/data/global_settlement_abi_v2_global_core_golden.json": "f266d82a3e2506cbb586c0fccffaa51218028c6fcbba84c493fc47d9f4ef05f2",
    "tests/data/global_settlement_abi_v2_asset_transfer_golden.json": "3a3f0a2edeb24daf088c3b44f48c6cea917880b8bba8a9702bed6c77e69ce52a",
    "tests/formal/test_lean_global_settlement_core_v2.py": "2f59fba46c7c42daab18053cb3ad22428825d7e7d649088e4e7c12d29a0a7b2d",
    "tests/formal/test_lean_asset_lane_refinement_v2.py": "1291a66f26638c835831e02612ce7d43814c91eb8cb1cc30ceaffa7443cce5cb",
}


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


@lru_cache(maxsize=None)
def _git_blob(repo_root: Path, subject: str, relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{subject}:{relative}"],
        cwd=repo_root,
        check=True,
        capture_output=True,
        timeout=15,
    )
    return result.stdout


def _subject_bytes(repo_root: Path, relative: str) -> bytes:
    return _git_blob(repo_root.resolve(), SUBJECT_COMMIT, relative)


def _subject_text(repo_root: Path, relative: str) -> str:
    return _subject_bytes(repo_root, relative).decode("utf-8")


def _is_mapping(value: object) -> bool:
    return isinstance(value, Mapping)


def _safe_repo_file(repo_root: Path, relative: str) -> Path:
    if not relative or Path(relative).is_absolute():
        raise ValueError(f"unsafe evidence path: {relative!r}")
    root = repo_root.resolve()
    path = (root / relative).resolve()
    if path != root and root not in path.parents:
        raise ValueError(f"evidence path escapes repository: {relative}")
    if not path.is_file():
        raise ValueError(f"evidence file missing: {relative}")
    return path


def _expect(condition: bool, message: str, errors: list[str]) -> None:
    if not condition:
        errors.append(message)


def _validate_subject(data: Mapping[str, Any], repo_root: Path, errors: list[str]) -> None:
    _expect(data.get("subject_commit") == SUBJECT_COMMIT, "subject commit mismatch", errors)
    try:
        result = subprocess.run(
            ["git", "merge-base", "--is-ancestor", SUBJECT_COMMIT, "HEAD"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=10,
        )
        _expect(result.returncode == 0, "frozen subject is not an ancestor of repository HEAD", errors)
    except (OSError, subprocess.SubprocessError) as exc:
        errors.append(f"could not validate frozen subject ancestry: {exc}")


def _validate_hashes(
    data: Mapping[str, Any], repo_root: Path, errors: list[str]
) -> list[str]:
    hashes = data.get("file_sha256")
    if not _is_mapping(hashes):
        errors.append("file_sha256 must be an object")
        return list(EXPECTED_HASHES)
    hashes = cast(Mapping[str, Any], hashes)
    _expect(dict(hashes) == EXPECTED_HASHES, "file hash registry differs from frozen inventory", errors)
    current_drift: list[str] = []
    for relative, expected in EXPECTED_HASHES.items():
        try:
            subject_blob = _subject_bytes(repo_root, relative)
            subject_actual = hashlib.sha256(subject_blob).hexdigest()
        except (OSError, subprocess.SubprocessError) as exc:
            errors.append(f"could not read frozen subject blob {relative}: {exc}")
            continue
        _expect(subject_actual == expected, f"frozen subject hash mismatch: {relative}", errors)
        try:
            current_actual = _sha256(_safe_repo_file(repo_root, relative))
        except (OSError, ValueError):
            current_drift.append(relative)
        else:
            if current_actual != expected:
                current_drift.append(relative)
    return current_drift


def _validate_record_source(
    name: str, source: object, repo_root: Path, errors: list[str]
) -> None:
    if not isinstance(source, str):
        return
    relative, separator, line_text = source.rpartition(":")
    try:
        line_number = int(line_text)
        source_lines = _subject_text(repo_root, relative).splitlines()
        declaration = source_lines[line_number - 1]
    except (OSError, UnicodeError, ValueError, IndexError, subprocess.SubprocessError):
        errors.append(f"{name}.source does not resolve at frozen subject")
        return
    _expect(
        separator == ":" and f"class {name}" in declaration,
        f"{name}.source does not anchor its class declaration",
        errors,
    )


def _validate_field_record(
    name: str,
    record: Mapping[str, Any],
    profiles: Mapping[str, Any],
    repo_root: Path,
    errors: list[str],
) -> None:
    expected_order = EXPECTED_PROJECTION_FIELD_ORDERS[name]
    for key in ("surface", "owner", "producer", "source", "order_kind", "rejection_boundary"):
        _expect(isinstance(record.get(key), str) and bool(record[key]), f"{name}.{key} missing", errors)
    _validate_record_source(name, record.get("source"), repo_root, errors)
    _expect(record.get("authority") == "NONE", f"{name} authority must be NONE", errors)
    fields = record.get("fields")
    if not isinstance(fields, list):
        errors.append(f"{name}.fields must be an array")
        return
    names = [field.get("name") if _is_mapping(field) else None for field in fields]
    _expect(names == expected_order, f"{name} projection/observable field order mismatch", errors)
    if name in GAP_NO_CANONICAL_ENCODER:
        _expect(record.get("serialization_status") == "GAP_NO_CANONICAL_ENCODER", f"{name} serialization gap status drift", errors)
        _expect("canonical_key_order_if_encoded" not in record, f"{name} must not claim canonical wire keys", errors)
    else:
        _expect(record.get("serialization_status") == "IMPLEMENTED_CANONICAL_ENCODER", f"{name} serialization status drift", errors)
        _expect(record.get("canonical_key_order_if_encoded") == sorted(expected_order), f"{name} canonical wire key order mismatch", errors)
    for field in fields:
        if not _is_mapping(field):
            errors.append(f"{name} has malformed field")
            continue
        _expect(set(field) >= {"name", "profile"}, f"{name} field metadata incomplete", errors)
        profile = field.get("profile")
        _expect(isinstance(profile, str) and profile in profiles, f"{name}.{field.get('name')} profile missing", errors)
        expected_profile = EXPECTED_FIELD_PROFILE_OVERRIDES.get((name, str(field.get("name"))))
        if expected_profile is not None:
            _expect(profile == expected_profile, f"{name}.{field.get('name')} field profile drift", errors)
    collection_key = record.get("collection_key")
    if not isinstance(collection_key, list) or not all(
        isinstance(item, str) for item in collection_key
    ):
        errors.append(f"{name}.collection_key must be an array of field names")
        return
    direct_keys = [item for item in collection_key if not item.startswith("derived:")]
    _expect(set(direct_keys).issubset(set(expected_order)), f"{name}.collection_key references unknown field", errors)
    if name in EXPECTED_COLLECTION_KEYS:
        _expect(collection_key == EXPECTED_COLLECTION_KEYS[name], f"{name}.collection_key drift", errors)


def _index_field_records(
    records: object, errors: list[str]
) -> dict[str, Mapping[str, Any]] | None:
    if not isinstance(records, list):
        errors.append("field_registry must be an array")
        return None
    by_name: dict[str, Mapping[str, Any]] = {}
    for record in records:
        if not _is_mapping(record) or not isinstance(record.get("record"), str):
            errors.append("field registry contains malformed record")
            continue
        name = record["record"]
        if name in by_name:
            errors.append(f"duplicate field registry record: {name}")
        by_name[name] = record
    return by_name


def _validate_profiles_and_records(
    data: Mapping[str, Any], repo_root: Path, errors: list[str]
) -> None:
    profiles = data.get("field_profiles")
    if not _is_mapping(profiles):
        errors.append("field_profiles must be an object")
        return
    profiles = cast(Mapping[str, Any], profiles)
    required_profile_keys = {"value_type", "unit", "width", "rejection"}
    for name, profile in profiles.items():
        if not _is_mapping(profile):
            errors.append(f"field profile {name} must be an object")
            continue
        _expect(set(profile) == required_profile_keys, f"field profile {name} has incomplete metadata", errors)
        _expect(all(isinstance(profile.get(key), str) and profile[key] for key in required_profile_keys), f"field profile {name} has empty metadata", errors)

    by_name = _index_field_records(data.get("field_registry"), errors)
    if by_name is None:
        return
    _expect(set(by_name) == set(EXPECTED_PROJECTION_FIELD_ORDERS), "field registry record inventory mismatch", errors)
    canonicalization = data.get("canonicalization")
    _expect(canonicalization == {
        "object_key_order": "UTF8_LEXICAL_ASCENDING",
        "registry_fields_order": "PROJECTION_FIELD_ORDER",
        "canonical_key_order_if_encoded_derivation": "sorted(fields[].name)",
        "array_order": "SEMANTIC_ORDER_AS_LISTED_OR_KEY_SORTED_BY_OWNING_TYPE",
    }, "canonicalization rule drift", errors)
    _expect(profiles.get("token") == {
        "value_type": "Python str / Rust String containing printable ASCII",
        "unit": "opaque identifier",
        "width": "1..160 printable ASCII bytes (0x21..0x7E)",
        "rejection": "typed constructor rejects empty, oversized, non-text, or non-printable values",
    }, "printable-ASCII token profile drift", errors)
    for collection_profile in ("ordered_records", "ordered_roots", "ordered_tokens"):
        profile = profiles.get(collection_profile)
        if _is_mapping(profile):
            profile = cast(Mapping[str, Any], profile)
            _expect(
                "no universal item bound asserted" in str(profile.get("width")),
                f"{collection_profile} overstates cardinality closure",
                errors,
            )
    for name in EXPECTED_PROJECTION_FIELD_ORDERS:
        record = by_name.get(name)
        if record is None:
            continue
        _validate_field_record(
            name,
            record,
            profiles,
            repo_root,
            errors,
        )


def _validate_lanes(data: Mapping[str, Any], errors: list[str]) -> None:
    lanes = data.get("lane_conservation_status")
    if not isinstance(lanes, list):
        errors.append("lane_conservation_status must be an array")
        return
    ids = [row.get("lane_id") if _is_mapping(row) else None for row in lanes]
    _expect(ids == EXPECTED_LANES, "lane inventory/order mismatch", errors)
    for row in lanes:
        if not _is_mapping(row):
            continue
        lane = row.get("lane_id")
        _expect(row.get("registered_global_lane") is True, f"{lane} must be registered", errors)
        _expect(row.get("exact_lane_write_coverage") is True, f"{lane} lane-write coverage drift", errors)
        _expect(row.get("structural_conservation_status") == "GLOBAL_AGGREGATE_RELATION_ONLY", f"{lane} structural status drift", errors)
        _expect(row.get("lane_semantic_status") == EXPECTED_LANE_SEMANTICS.get(str(lane)), f"{lane} semantic status drift", errors)
        _expect(row.get("mounted") is False, f"{lane} mounting claim forbidden", errors)
        _expect(row.get("release_backed") is False, f"{lane} release claim forbidden", errors)
        _expect(row.get("production_authority") == "NONE", f"{lane} authority must be NONE", errors)


def _validate_enums(data: Mapping[str, Any], repo_root: Path, errors: list[str]) -> None:
    inventory = data.get("enum_inventory")
    _expect(inventory == EXPECTED_ENUMS, "enum inventory mismatch", errors)
    python_sources = {
        "LaneIdV2": "src/core/global_settlement_primitives_v2.py",
        "EconomicEffectKindV2": "src/core/global_settlement_effect_values_v2.py",
        "TerminalObligationStatusV2": "src/core/global_settlement_lifecycle_v2.py",
        "OutboxStatusV2": "src/core/global_economic_state_ownership_v2.py",
        "GlobalEconomicRefinementRejectCodeV2": "src/core/global_economic_refinement_outcome_v2.py",
        "AssetClassV2": "src/core/asset_transfer_types_v2.py",
        "AssetTransferRejectCodeV2": "src/core/asset_transfer_types_v2.py",
        "ManagedAssetLifecycleRejectCodeV2": "src/core/managed_asset_lifecycle_result_v2.py",
        "AssetLaneRouteV2": "src/core/asset_lane_coordinator_values_v2.py",
        "AssetLaneCoordinatorRejectCodeV2": "src/core/asset_lane_coordinator_values_v2.py",
        "AssetOriginKindV2": "src/core/asset_origin_registry_types_v2.py",
        "AssetOriginRegistrationRejectCodeV2": "src/core/asset_origin_registry_types_v2.py",
    }
    for enum_name, relative in python_sources.items():
        text = _subject_text(repo_root, relative)
        positions = [text.find(f'"{value}"') for value in EXPECTED_ENUMS[enum_name]]
        _expect(all(position >= 0 for position in positions), f"Python enum member drift: {enum_name}", errors)
        _expect(positions == sorted(positions), f"Python enum order drift: {enum_name}", errors)
    global_rust = _subject_text(repo_root, "zk/global_settlement_abi_v2/src/outcome.rs")
    transfer_rust = _subject_text(repo_root, "zk/global_settlement_abi_v2/src/asset_transfer_types.rs")
    for value in EXPECTED_ENUMS["AssetTransferRejectCodeV2"]:
        _expect(value in transfer_rust, f"Rust asset-transfer reject missing: {value}", errors)
    for value in EXPECTED_ENUMS["GlobalEconomicRefinementRejectCodeV2"]:
        _expect(value in global_rust, f"Rust global reject sentinel missing: {value}", errors)


def _validate_fixtures(data: Mapping[str, Any], repo_root: Path, errors: list[str]) -> None:
    fixtures = data.get("fixtures")
    expected = {
        "tests/data/global_settlement_abi_v2_global_core_golden.json": (
            "zenodex/global-settlement-abi-v2-global-core-golden/v1",
            ["effect_plan", "occurrence", "oracle_plan", "post_state", "pre_state", "terminal_plan"],
        ),
        "tests/data/global_settlement_abi_v2_asset_transfer_golden.json": (
            "zenodex/global-settlement-abi-v2-asset-transfer-golden/v1",
            ["command", "context", "effect_plan", "module_journal", "occurrence", "post_state", "pre_state"],
        ),
    }
    if not isinstance(fixtures, list):
        errors.append("fixtures must be an array")
        return
    by_path = {row.get("path"): row for row in fixtures if _is_mapping(row)}
    _expect(set(by_path) == set(expected), "fixture inventory mismatch", errors)
    for relative, (schema, vectors) in expected.items():
        row = by_path.get(relative)
        if row is None:
            continue
        _expect(row.get("sha256") == EXPECTED_HASHES[relative], f"fixture hash registry mismatch: {relative}", errors)
        try:
            fixture = json.loads(_subject_text(repo_root, relative))
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"invalid fixture {relative}: {exc}")
            continue
        _expect(fixture.get("fixture_schema") == schema, f"fixture schema drift: {relative}", errors)
        _expect(fixture.get("authority") == "NONE", f"fixture authority drift: {relative}", errors)
        _expect(list(fixture.get("vectors", {})) == vectors, f"fixture vector inventory/order drift: {relative}", errors)


def _validate_formal(data: Mapping[str, Any], repo_root: Path, errors: list[str]) -> None:
    formal = data.get("formal_evidence")
    if not _is_mapping(formal):
        errors.append("formal_evidence must be an object")
        return
    formal = cast(Mapping[str, Any], formal)
    _expect(formal.get("toolchain") == "leanprover/lean4:v4.27.0", "Lean toolchain mismatch", errors)
    _expect(formal.get("authority") == "NONE", "formal authority must be NONE", errors)
    _expect(formal.get("theorems") == EXPECTED_FORMAL_THEOREMS, "formal theorem inventory mismatch", errors)
    for relative, names in EXPECTED_FORMAL_THEOREMS.items():
        text = _subject_text(repo_root, relative)
        for forbidden in ("sorry", "admit", "axiom"):
            _expect(re.search(rf"\b{forbidden}\b", text, flags=re.IGNORECASE) is None, f"forbidden Lean placeholder in {relative}: {forbidden}", errors)
        for name in names:
            _expect(f"theorem {name}" in text, f"formal theorem missing: {relative}:{name}", errors)


def _validate_plan_and_claims(data: Mapping[str, Any], repo_root: Path, errors: list[str]) -> None:
    _expect(data.get("schema") == SCHEMA, "schema mismatch", errors)
    _expect(data.get("obligation") == "O-008", "obligation must be O-008", errors)
    _expect(data.get("evidence_status") == "BOUNDED_CORE_EVIDENCE_ONLY", "evidence status drift", errors)
    _expect(data.get("promotion_allowed") is False, "O-008 promotion must remain false", errors)
    _expect(data.get("authority") == "NONE", "packet authority must be NONE", errors)
    _expect(data.get("dependencies") == EXPECTED_DEPENDENCIES, "dependency status drift", errors)
    _expect(data.get("nonclaims") == EXPECTED_NONCLAIMS, "nonclaim inventory mismatch", errors)
    gates = data.get("whole_program_value_movement_gates")
    _expect(gates == {"total": 12, "passed": 0, "closed": 0, "status": "OPEN_UNVERIFIED"}, "value-movement gate posture drift", errors)
    _expect(data.get("typed_reject_no_op_status") == {
        "global": "IMPLEMENTED_TESTED_AND_BOUNDED_LEAN",
        "asset_transfer": "IMPLEMENTED_TESTED_AND_BOUNDED_LEAN",
        "managed_asset_lifecycle": "IMPLEMENTED_TESTED_AND_BOUNDED_LEAN_PYTHON_ONLY",
        "asset_lane_coordinator": "IMPLEMENTED_TESTED_PYTHON_ONLY",
        "authority": "NONE",
    }, "typed reject/no-op status drift", errors)
    _expect(data.get("python_rust_parity_scope") == {
        "global_core": "CANONICAL_FIXTURE_AND_WIRE_CODE_SET",
        "asset_transfer": "CANONICAL_FIXTURE_AND_TRANSITION_SLICE",
        "managed_asset_lifecycle": "GAP_NO_RUST_V2_IMPLEMENTATION",
        "asset_lane_coordinator": "GAP_NO_RUST_V2_IMPLEMENTATION",
        "claim": "BOUNDED_SUBJECT_PINNED_PARITY_ONLY",
    }, "Python/Rust parity scope drift", errors)
    _expect(data.get("collection_bound_completeness") == {
        "status": "GAP_NOT_FULLY_CLASSIFIED",
        "global_core": "MIXED_EXPLICIT_AND_UNBOUNDED_COLLECTIONS",
        "asset_slice": "MIXED_EXPLICIT_AND_NO_EXPLICIT_ITEM_BOUND",
        "claim": "No universal item ceiling is asserted; each collection inherits only bounds explicitly enforced by its owning source.",
    }, "collection-bound completeness gap drift", errors)
    equations = data.get("equations")
    _expect(isinstance(equations, list) and [row.get("id") for row in equations if _is_mapping(row)] == EXPECTED_EQUATIONS, "equation inventory mismatch", errors)
    if isinstance(equations, list):
        for row in equations:
            if not _is_mapping(row):
                errors.append("malformed equation row")
                continue
            _expect(all(isinstance(row.get(key), str) and row[key] for key in ("id", "formula", "scope", "source")), f"equation {row.get('id')} incomplete", errors)
            _expect(row.get("source") == EXPECTED_EQUATION_SOURCES.get(str(row.get("id"))), f"equation {row.get('id')} source drift", errors)

    try:
        plan = json.loads(_subject_text(repo_root, "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"))
        plan_gates = plan.get("value_movement_gates")
        _expect(isinstance(plan_gates, list) and len(plan_gates) == 12, "plan no longer has exactly 12 value-movement gates", errors)
        _expect(isinstance(plan_gates, list) and sum(row.get("status") == "PASS" for row in plan_gates) == 0, "plan gate pass count is no longer zero", errors)
        obligations = {row.get("obligation_id"): row for row in plan.get("next_obligations", [])}
        _expect(obligations.get("O-008", {}).get("depends_on") == ["O-006", "O-007C", "O-008A"], "O-008 plan dependency drift", errors)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        errors.append(f"could not validate whole-program plan: {exc}")


def check_evidence_manifest(
    manifest_path: Path = MANIFEST_PATH,
    *,
    repo_root: Path = REPO_ROOT,
) -> dict[str, Any]:
    """Validate a packet while preserving its explicit zero-authority posture."""

    errors: list[str] = []
    try:
        loaded = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        loaded = {}
        errors.append(f"could not load manifest: {exc}")
    if not _is_mapping(loaded):
        errors.append("manifest root must be an object")
        data: Mapping[str, Any] = {}
    else:
        data = loaded

    _validate_subject(data, repo_root, errors)
    _validate_plan_and_claims(data, repo_root, errors)
    current_drift = _validate_hashes(data, repo_root, errors)
    _validate_profiles_and_records(data, repo_root, errors)
    _validate_lanes(data, errors)
    _validate_enums(data, repo_root, errors)
    _validate_fixtures(data, repo_root, errors)
    _validate_formal(data, repo_root, errors)

    ok = not errors
    return {
        "schema": REPORT_SCHEMA,
        "ok": ok,
        "status": "BOUNDED_EVIDENCE_VALID_NO_PROMOTION" if ok else "INVALID_FAIL_CLOSED",
        "subject_commit": SUBJECT_COMMIT,
        "obligation": "O-008",
        "promotion_allowed": False,
        "authority": "NONE",
        "whole_program_value_movement_gates_passed": 0,
        "current_applicable": not current_drift,
        "current_source_drift": current_drift,
        "errors": errors,
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", nargs="?", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    try:
        report = check_evidence_manifest(args.manifest, repo_root=args.repo_root)
    except Exception as exc:  # defensive CLI boundary; failure remains closed
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "INVALID_FAIL_CLOSED",
            "subject_commit": SUBJECT_COMMIT,
            "obligation": "O-008",
            "promotion_allowed": False,
            "authority": "NONE",
            "whole_program_value_movement_gates_passed": 0,
            "errors": [f"unexpected checker failure: {type(exc).__name__}: {exc}"],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
