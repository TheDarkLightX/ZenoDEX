"""Closed source-owned policy for M5-P4B0 legacy refinement."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import final

from ..state.canonical import canonical_json_bytes, sha256_hex
from ..state.intents import IntentKind
from .fcis_legacy_refinement_values import ObservationResultKindV1

POLICY_VERSION_V1 = "zenodex/fcis-m5-p4b0-refinement-policy/v1"
LEGACY_ALGORITHM_ID_V1 = "legacy_dex_step"
EXACT_ALGORITHM_ID_V1 = "zenodex/fcis/spot-step-evaluator/v1"
SEMANTIC_STATE_PROJECTION_VERSION_V1 = 1
ECONOMIC_OUTPUT_PROJECTION_VERSION_V1 = 1
PATCH_CHECK_VERSION_V1 = 1
RECEIPT_BUNDLE_CHECK_VERSION_V1 = 1
REPLAY_OUTBOX_CHECK_VERSION_V1 = 1
BUDGET_HASH_V1 = "0xa2e946a9065ea6a1d96279b5899219b04aeae939df457d3196074256745f95b6"
SEMANTIC_STATE_FIELD_ORDER_V1 = (
    "balances",
    "pools",
    "lp_balances",
    "nonces",
    "vault",
    "oracle",
    "fee_accumulator",
    "perps",
)


class ExactOnlyFieldKindV1(Enum):
    BYTES = "bytes"
    DIGEST = "digest"
    IDENTITIES = "identities"


class RejectionReasonRuleV1(Enum):
    EXACT_EQUAL = "exact_equal"


@final
@dataclass(frozen=True, slots=True)
class VersionDeltaEntryV1:
    stable_id: str
    field_name: str
    legacy_value: str
    exact_value: str
    result_kind: ObservationResultKindV1


@final
@dataclass(frozen=True, slots=True)
class RejectionMappingV1:
    stable_id: str
    legacy_code: str
    legacy_precedence: str
    exact_code: str
    exact_phase: str
    exact_precedence: str
    path_rule: str
    reason_rule: RejectionReasonRuleV1
    lost_distinction_authoritative: bool


@final
@dataclass(frozen=True, slots=True)
class ExactOnlyFieldEntryV1:
    stable_id: str
    field_name: str
    field_kind: ExactOnlyFieldKindV1


@final
@dataclass(frozen=True, slots=True)
class SemanticProjectionEntryV1:
    stable_id: str
    projection_name: str
    version: int


@final
@dataclass(frozen=True, slots=True)
class CommandKindEntryV1:
    stable_id: str
    command_kind: str


def _version_entries(
    result_kind: ObservationResultKindV1,
    suffix: str,
    snapshot_exact: str,
    support_exact: str,
) -> tuple[VersionDeltaEntryV1, ...]:
    return (
        VersionDeltaEntryV1(
            f"version.algorithm_id.{suffix}",
            "algorithm_id",
            LEGACY_ALGORITHM_ID_V1,
            EXACT_ALGORITHM_ID_V1,
            result_kind,
        ),
        VersionDeltaEntryV1(
            f"version.algorithm_version.{suffix}",
            "algorithm_version",
            "1",
            "1",
            result_kind,
        ),
        VersionDeltaEntryV1(
            f"version.codec_version.{suffix}",
            "codec_version",
            "1",
            "1",
            result_kind,
        ),
        VersionDeltaEntryV1(
            f"version.schema_version.{suffix}",
            "schema_version",
            "1",
            "1",
            result_kind,
        ),
        VersionDeltaEntryV1(
            f"version.snapshot_version.{suffix}",
            "snapshot_version",
            "4",
            snapshot_exact,
            result_kind,
        ),
        VersionDeltaEntryV1(
            f"version.support_root_version.{suffix}",
            "support_root_version",
            "4",
            support_exact,
            result_kind,
        ),
    )


VERSION_DELTA_ENTRIES_V1 = _version_entries(
    ObservationResultKindV1.ACCEPT,
    "accept",
    "4",
    "5",
) + _version_entries(
    ObservationResultKindV1.REJECT,
    "reject",
    "none",
    "none",
)

REJECTION_MAPPINGS_V1 = (
    RejectionMappingV1(
        "reject.pool_not_found",
        "POOL_NOT_FOUND",
        "settlement_or_policy",
        "rejected_intent",
        "settlement",
        "settlement",
        "exact_equal",
        RejectionReasonRuleV1.EXACT_EQUAL,
        False,
    ),
    RejectionMappingV1(
        "reject.pool_already_exists",
        "POOL_ALREADY_EXISTS",
        "settlement_or_policy",
        "rejected_intent",
        "settlement",
        "settlement",
        "exact_equal",
        RejectionReasonRuleV1.EXACT_EQUAL,
        False,
    ),
    RejectionMappingV1(
        "reject.insufficient_lp",
        "INSUFFICIENT_LP",
        "settlement_or_policy",
        "rejected_intent",
        "settlement",
        "settlement",
        "exact_equal",
        RejectionReasonRuleV1.EXACT_EQUAL,
        False,
    ),
    RejectionMappingV1(
        "reject.insufficient_balance",
        "INSUFFICIENT_BALANCE",
        "settlement_or_policy",
        "rejected_intent",
        "settlement",
        "settlement",
        "exact_equal",
        RejectionReasonRuleV1.EXACT_EQUAL,
        False,
    ),
    RejectionMappingV1(
        "reject.slippage",
        "SLIPPAGE",
        "settlement_or_policy",
        "rejected_intent",
        "settlement",
        "settlement",
        "exact_equal",
        RejectionReasonRuleV1.EXACT_EQUAL,
        False,
    ),
    RejectionMappingV1(
        "reject.legacy_string.settlement",
        "LEGACY_STRING_ERROR",
        "settlement_or_policy",
        "strong_settlement_rejected",
        "settlement",
        "settlement",
        "exact_equal",
        RejectionReasonRuleV1.EXACT_EQUAL,
        False,
    ),
    RejectionMappingV1(
        "reject.legacy_string.nonce",
        "LEGACY_STRING_ERROR",
        "nonce",
        "invalid_nonce",
        "nonce",
        "nonce",
        "exact_equal",
        RejectionReasonRuleV1.EXACT_EQUAL,
        False,
    ),
)

EXACT_ONLY_FIELD_ENTRIES_V1 = (
    ExactOnlyFieldEntryV1("exact.bundle_bytes", "bundle_bytes", ExactOnlyFieldKindV1.BYTES),
    ExactOnlyFieldEntryV1("exact.bundle_root", "bundle_root", ExactOnlyFieldKindV1.DIGEST),
    ExactOnlyFieldEntryV1(
        "exact.commit_plan_bytes",
        "commit_plan_bytes",
        ExactOnlyFieldKindV1.BYTES,
    ),
    ExactOnlyFieldEntryV1("exact.effects_bytes", "effects_bytes", ExactOnlyFieldKindV1.BYTES),
    ExactOnlyFieldEntryV1("exact.outbox_bytes", "outbox_bytes", ExactOnlyFieldKindV1.BYTES),
    ExactOnlyFieldEntryV1(
        "exact.outbox_identities",
        "outbox_identities",
        ExactOnlyFieldKindV1.IDENTITIES,
    ),
    ExactOnlyFieldEntryV1("exact.patch_bytes", "patch_bytes", ExactOnlyFieldKindV1.BYTES),
    ExactOnlyFieldEntryV1("exact.receipt_bytes", "receipt_bytes", ExactOnlyFieldKindV1.BYTES),
    ExactOnlyFieldEntryV1("exact.receipt_root", "receipt_root", ExactOnlyFieldKindV1.DIGEST),
    ExactOnlyFieldEntryV1("exact.replay_bytes", "replay_bytes", ExactOnlyFieldKindV1.BYTES),
)

SEMANTIC_PROJECTION_ENTRIES_V1 = (
    SemanticProjectionEntryV1(
        "projection.state",
        "eight_committed_state_fields",
        SEMANTIC_STATE_PROJECTION_VERSION_V1,
    ),
    SemanticProjectionEntryV1(
        "projection.economic",
        "ordered_economic_outputs",
        ECONOMIC_OUTPUT_PROJECTION_VERSION_V1,
    ),
    SemanticProjectionEntryV1("projection.patch", "patch_consistency", PATCH_CHECK_VERSION_V1),
    SemanticProjectionEntryV1(
        "projection.receipt_bundle",
        "receipt_bundle_binding",
        RECEIPT_BUNDLE_CHECK_VERSION_V1,
    ),
    SemanticProjectionEntryV1(
        "projection.replay_outbox",
        "replay_outbox_consistency",
        REPLAY_OUTBOX_CHECK_VERSION_V1,
    ),
)

COMMAND_KIND_ENTRIES_V1 = (
    CommandKindEntryV1("command.create_pool", "CREATE_POOL"),
    CommandKindEntryV1("command.add_liquidity", "ADD_LIQUIDITY"),
    CommandKindEntryV1("command.remove_liquidity", "REMOVE_LIQUIDITY"),
    CommandKindEntryV1("command.swap_exact_in", "SWAP_EXACT_IN"),
    CommandKindEntryV1("command.swap_exact_out", "SWAP_EXACT_OUT"),
    CommandKindEntryV1("command.route_exact_in", "ROUTE_EXACT_IN"),
    CommandKindEntryV1("command.route_exact_out", "ROUTE_EXACT_OUT"),
)


def lookup_version_delta_v1(
    field_name: str,
    legacy_value: str,
    exact_value: str,
    result_kind: ObservationResultKindV1,
) -> VersionDeltaEntryV1 | None:
    for entry in VERSION_DELTA_ENTRIES_V1:
        if (
            entry.field_name == field_name
            and entry.legacy_value == legacy_value
            and entry.exact_value == exact_value
            and entry.result_kind is result_kind
        ):
            return entry
    return None


def lookup_rejection_mapping_v1(
    legacy_code: str,
    legacy_precedence: str,
) -> RejectionMappingV1 | None:
    for entry in REJECTION_MAPPINGS_V1:
        if entry.legacy_code == legacy_code and entry.legacy_precedence == legacy_precedence:
            return entry
    return None


def is_known_command_kind_v1(command_kind: str) -> bool:
    return any(entry.command_kind == command_kind for entry in COMMAND_KIND_ENTRIES_V1)


def _policy_payload_v1() -> bytes:
    return canonical_json_bytes(
        {
            "budget_hash": BUDGET_HASH_V1,
            "command_kinds": [
                {"command_kind": entry.command_kind, "stable_id": entry.stable_id}
                for entry in COMMAND_KIND_ENTRIES_V1
            ],
            "exact_only_fields": [
                {
                    "field_kind": entry.field_kind.value,
                    "field_name": entry.field_name,
                    "stable_id": entry.stable_id,
                }
                for entry in EXACT_ONLY_FIELD_ENTRIES_V1
            ],
            "policy_version": POLICY_VERSION_V1,
            "semantic_state_field_order": list(SEMANTIC_STATE_FIELD_ORDER_V1),
            "projections": [
                {
                    "projection_name": entry.projection_name,
                    "stable_id": entry.stable_id,
                    "version": entry.version,
                }
                for entry in SEMANTIC_PROJECTION_ENTRIES_V1
            ],
            "rejection_mappings": [
                {
                    "exact_code": entry.exact_code,
                    "exact_phase": entry.exact_phase,
                    "exact_precedence": entry.exact_precedence,
                    "legacy_code": entry.legacy_code,
                    "legacy_precedence": entry.legacy_precedence,
                    "lost_distinction_authoritative": entry.lost_distinction_authoritative,
                    "path_rule": entry.path_rule,
                    "reason_rule": entry.reason_rule.value,
                    "stable_id": entry.stable_id,
                }
                for entry in REJECTION_MAPPINGS_V1
            ],
            "version_deltas": [
                {
                    "exact_value": entry.exact_value,
                    "field_name": entry.field_name,
                    "legacy_value": entry.legacy_value,
                    "result_kind": entry.result_kind.value,
                    "stable_id": entry.stable_id,
                }
                for entry in VERSION_DELTA_ENTRIES_V1
            ],
        }
    )


POLICY_HASH_V1 = sha256_hex(_policy_payload_v1())


def _validate_registry_v1() -> None:
    stable_ids = (
        *(entry.stable_id for entry in VERSION_DELTA_ENTRIES_V1),
        *(entry.stable_id for entry in REJECTION_MAPPINGS_V1),
        *(entry.stable_id for entry in EXACT_ONLY_FIELD_ENTRIES_V1),
        *(entry.stable_id for entry in SEMANTIC_PROJECTION_ENTRIES_V1),
        *(entry.stable_id for entry in COMMAND_KIND_ENTRIES_V1),
    )
    if len(stable_ids) != len(set(stable_ids)):
        raise RuntimeError("P4B0 policy stable IDs are not unique")
    version_keys = tuple(
        (entry.field_name, entry.legacy_value, entry.exact_value, entry.result_kind)
        for entry in VERSION_DELTA_ENTRIES_V1
    )
    if len(version_keys) != len(set(version_keys)):
        raise RuntimeError("P4B0 version-delta keys are not unique")
    rejection_keys = tuple(
        (entry.legacy_code, entry.legacy_precedence) for entry in REJECTION_MAPPINGS_V1
    )
    if len(rejection_keys) != len(set(rejection_keys)):
        raise RuntimeError("P4B0 rejection mapping keys are not unique")
    exact_fields = tuple(entry.field_name for entry in EXACT_ONLY_FIELD_ENTRIES_V1)
    if len(exact_fields) != len(set(exact_fields)):
        raise RuntimeError("P4B0 exact-only fields are not unique")
    declared_commands = {entry.command_kind for entry in COMMAND_KIND_ENTRIES_V1}
    source_commands = {member.value for member in IntentKind}
    if declared_commands != source_commands:
        raise RuntimeError("P4B0 command registry does not cover IntentKind exactly")
    if any(entry.lost_distinction_authoritative for entry in REJECTION_MAPPINGS_V1):
        raise RuntimeError("P4B0 policy cannot erase an authoritative rejection distinction")


_validate_registry_v1()


__all__ = (
    "BUDGET_HASH_V1",
    "COMMAND_KIND_ENTRIES_V1",
    "ECONOMIC_OUTPUT_PROJECTION_VERSION_V1",
    "EXACT_ALGORITHM_ID_V1",
    "EXACT_ONLY_FIELD_ENTRIES_V1",
    "LEGACY_ALGORITHM_ID_V1",
    "PATCH_CHECK_VERSION_V1",
    "POLICY_HASH_V1",
    "POLICY_VERSION_V1",
    "RECEIPT_BUNDLE_CHECK_VERSION_V1",
    "REJECTION_MAPPINGS_V1",
    "REPLAY_OUTBOX_CHECK_VERSION_V1",
    "SEMANTIC_PROJECTION_ENTRIES_V1",
    "SEMANTIC_STATE_FIELD_ORDER_V1",
    "SEMANTIC_STATE_PROJECTION_VERSION_V1",
    "VERSION_DELTA_ENTRIES_V1",
    "CommandKindEntryV1",
    "ExactOnlyFieldEntryV1",
    "ExactOnlyFieldKindV1",
    "RejectionMappingV1",
    "RejectionReasonRuleV1",
    "SemanticProjectionEntryV1",
    "VersionDeltaEntryV1",
    "is_known_command_kind_v1",
    "lookup_rejection_mapping_v1",
    "lookup_version_delta_v1",
)
