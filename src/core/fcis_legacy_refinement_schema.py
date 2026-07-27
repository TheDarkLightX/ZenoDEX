"""Closed declarative schemas for unmounted M5-P4B0 evidence.

All structural choices are trusted source data.  Authority bytes cannot choose
schemas, constructors, registries, resolvers, encoders, or policy entries.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import final

from ..state.snapshot_combinators import (
    AdmissionLimitsV1,
    DeclaredFieldV1,
    ExactInt,
    ExactKeyedMap,
    ExactString,
    OptionalValue,
    SchemaRegistrationV1,
    SchemaV1,
    SequenceOf,
    SequenceSourceKind,
    StringRuleV1,
)

REFINEMENT_SCHEMA_REVISION_V1 = "zenodex/fcis-m5-p4b0-refinement-schema/v1"

INPUT_BINDING_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/input-binding/v1"
REJECTION_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/rejection/v1"
FEE_ALLOCATION_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/fee-allocation/v1"
UNAVAILABLE_MARKER_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/unavailable/v1"
OUTBOX_IDENTITY_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/outbox-identity/v1"
LEGACY_OBSERVATION_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/legacy-observation/v1"
EXACT_OBSERVATION_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/exact-observation/v1"
LEGACY_BOUND_OBSERVATION_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/legacy-bound/v1"
EXACT_BOUND_OBSERVATION_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/exact-bound/v1"
OBSERVATION_PAIR_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/observation-pair/v1"

MAX_REFINEMENT_BYTES_V1 = 512_000
MAX_REFINEMENT_DEPTH_V1 = 64
MAX_REFINEMENT_NODES_V1 = 50_000
MAX_REFINEMENT_FIXTURES_V1 = 24
MAX_REFINEMENT_OBSERVATIONS_V1 = 48
MAX_REFINEMENT_COLLECTION_ITEMS_V1 = 512
MAX_REFINEMENT_FIELD_UTF8_BYTES_V1 = 262_144
MAX_REFINEMENT_TEXT_UTF8_BYTES_V1 = 16_384
MAX_REFINEMENT_MISMATCH_PAYLOAD_BYTES_V1 = 4_096
MAX_REFINEMENT_WITNESS_BYTES_V1 = 8_192
MAX_REFINEMENT_COMMAND_PARTS_V1 = 64
MAX_REFINEMENT_PATH_PARTS_V1 = 64
MAX_REFINEMENT_OUTBOX_IDENTITIES_V1 = 512
MAX_REFINEMENT_SCALAR_V1 = (1 << 256) - 1


class RefinementEnumTagV1(Enum):
    """Empty closed tag family because decoded evidence contains no Python enum."""


class RefinementRecordTagV1(Enum):
    """Empty closed tag family because evidence uses exact keyed-map schemas."""


def _field(name: str, schema: SchemaV1) -> DeclaredFieldV1:
    return DeclaredFieldV1(name, schema)


NONNEGATIVE_V1 = ExactInt(0, MAX_REFINEMENT_SCALAR_V1)
TEXT_V1 = ExactString(
    StringRuleV1.NON_EMPTY,
    MAX_REFINEMENT_TEXT_UTF8_BYTES_V1,
    max_characters=MAX_REFINEMENT_TEXT_UTF8_BYTES_V1,
)
SHORT_TEXT_V1 = ExactString(StringRuleV1.NON_EMPTY, 4_096, max_characters=4_096)
RESULT_KIND_TEXT_V1 = ExactString(StringRuleV1.NON_EMPTY, 16, max_characters=16)
HEX_BYTES_V1 = ExactString(
    StringRuleV1.LOWERCASE_HEX,
    MAX_REFINEMENT_FIELD_UTF8_BYTES_V1,
    max_characters=MAX_REFINEMENT_FIELD_UTF8_BYTES_V1,
)
DIGEST_V1 = ExactString(
    StringRuleV1.LOWERCASE_0X_HEX,
    66,
    exact_utf8_bytes=66,
    max_characters=66,
)
GIT_OBJECT_ID_V1 = ExactString(
    StringRuleV1.LOWERCASE_HEX,
    40,
    exact_utf8_bytes=40,
    max_characters=40,
)
UNAVAILABLE_LITERAL_V1 = ExactString(
    StringRuleV1.EXACT_LITERAL,
    24,
    exact_literal="UNAVAILABLE_IN_LEGACY_V1",
    exact_utf8_bytes=24,
    max_characters=24,
)
STRING_SEQUENCE_V1 = SequenceOf(
    (SequenceSourceKind.EXACT_LIST,),
    SHORT_TEXT_V1,
    0,
    MAX_REFINEMENT_COLLECTION_ITEMS_V1,
)
COMMAND_BYTES_SEQUENCE_V1 = SequenceOf(
    (SequenceSourceKind.EXACT_LIST,),
    HEX_BYTES_V1,
    1,
    MAX_REFINEMENT_COMMAND_PARTS_V1,
)
UNAVAILABLE_MARKER_SCHEMA_V1 = ExactKeyedMap(
    (_field("status", UNAVAILABLE_LITERAL_V1),),
    UNAVAILABLE_MARKER_SCHEMA_ID_V1,
)

REJECTION_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("code", SHORT_TEXT_V1),
        _field(
            "path",
            SequenceOf(
                (SequenceSourceKind.EXACT_LIST,),
                SHORT_TEXT_V1,
                0,
                MAX_REFINEMENT_PATH_PARTS_V1,
            ),
        ),
        _field("precedence", SHORT_TEXT_V1),
        _field("public_reason", TEXT_V1),
        _field("unavailable_fields", STRING_SEQUENCE_V1),
    ),
    REJECTION_SCHEMA_ID_V1,
)

FEE_ALLOCATION_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("buyback_amount", NONNEGATIVE_V1),
        _field("dust_carried", NONNEGATIVE_V1),
        _field("rewards_amount", NONNEGATIVE_V1),
        _field("treasury_amount", NONNEGATIVE_V1),
    ),
    FEE_ALLOCATION_SCHEMA_ID_V1,
)

OUTBOX_IDENTITY_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("effect_identity", DIGEST_V1),
        _field("effect_index", NONNEGATIVE_V1),
        _field("idempotency_key", DIGEST_V1),
    ),
    OUTBOX_IDENTITY_SCHEMA_ID_V1,
)
OUTBOX_IDENTITIES_SEQUENCE_V1 = SequenceOf(
    (SequenceSourceKind.EXACT_LIST,),
    OUTBOX_IDENTITY_SCHEMA_V1,
    0,
    MAX_REFINEMENT_OUTBOX_IDENTITIES_V1,
)

INPUT_BINDING_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("baseline_artifact_hash", DIGEST_V1),
        _field("differential_artifact_hash", DIGEST_V1),
        _field("reviewed_start_sha", GIT_OBJECT_ID_V1),
        _field("packet_commit", GIT_OBJECT_ID_V1),
        _field("packet_tree_hash", GIT_OBJECT_ID_V1),
        _field("fixture_id", SHORT_TEXT_V1),
        _field("command_kind", SHORT_TEXT_V1),
        _field("command_bytes", COMMAND_BYTES_SEQUENCE_V1),
        _field("command_hash", DIGEST_V1),
        _field("pre_state_bytes", HEX_BYTES_V1),
        _field("pre_state_root", DIGEST_V1),
        _field("context_bytes", HEX_BYTES_V1),
        _field("context_hash", DIGEST_V1),
    ),
    INPUT_BINDING_SCHEMA_ID_V1,
)


def _common_observation_fields() -> tuple[DeclaredFieldV1, ...]:
    return (
        _field("algorithm_id", SHORT_TEXT_V1),
        _field("algorithm_version", NONNEGATIVE_V1),
        _field("codec_version", NONNEGATIVE_V1),
        _field("schema_version", NONNEGATIVE_V1),
        _field("snapshot_version", OptionalValue(NONNEGATIVE_V1)),
        _field("support_root_version", OptionalValue(NONNEGATIVE_V1)),
        _field("result_kind", RESULT_KIND_TEXT_V1),
        _field("rejection", OptionalValue(REJECTION_SCHEMA_V1)),
        _field("next_state_snapshot_bytes", OptionalValue(HEX_BYTES_V1)),
        _field("next_state_snapshot_root", OptionalValue(DIGEST_V1)),
        _field("next_nonce_table_hash", OptionalValue(DIGEST_V1)),
        _field("settlement_bytes", OptionalValue(HEX_BYTES_V1)),
        _field("support_root", OptionalValue(DIGEST_V1)),
        _field("total_swap_fees", OptionalValue(NONNEGATIVE_V1)),
        _field("fee_allocation", OptionalValue(FEE_ALLOCATION_SCHEMA_V1)),
    )


def _legacy_exact_only_fields() -> tuple[DeclaredFieldV1, ...]:
    marker = OptionalValue(UNAVAILABLE_MARKER_SCHEMA_V1)
    return (
        _field("bundle_bytes", marker),
        _field("bundle_root", marker),
        _field("commit_plan_bytes", marker),
        _field("effects_bytes", marker),
        _field("outbox_bytes", marker),
        _field("outbox_identities", marker),
        _field("patch_bytes", marker),
        _field("receipt_bytes", marker),
        _field("receipt_root", marker),
        _field("replay_bytes", marker),
    )


def _exact_exact_only_fields() -> tuple[DeclaredFieldV1, ...]:
    return (
        _field("bundle_bytes", OptionalValue(HEX_BYTES_V1)),
        _field("bundle_root", OptionalValue(DIGEST_V1)),
        _field("commit_plan_bytes", OptionalValue(HEX_BYTES_V1)),
        _field("effects_bytes", OptionalValue(HEX_BYTES_V1)),
        _field("outbox_bytes", OptionalValue(HEX_BYTES_V1)),
        _field("outbox_identities", OptionalValue(OUTBOX_IDENTITIES_SEQUENCE_V1)),
        _field("patch_bytes", OptionalValue(HEX_BYTES_V1)),
        _field("receipt_bytes", OptionalValue(HEX_BYTES_V1)),
        _field("receipt_root", OptionalValue(DIGEST_V1)),
        _field("replay_bytes", OptionalValue(HEX_BYTES_V1)),
    )


LEGACY_OBSERVATION_SCHEMA_V1 = ExactKeyedMap(
    _common_observation_fields() + _legacy_exact_only_fields(),
    LEGACY_OBSERVATION_SCHEMA_ID_V1,
)
EXACT_OBSERVATION_SCHEMA_V1 = ExactKeyedMap(
    _common_observation_fields() + _exact_exact_only_fields(),
    EXACT_OBSERVATION_SCHEMA_ID_V1,
)
LEGACY_BOUND_OBSERVATION_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("binding", INPUT_BINDING_SCHEMA_V1),
        _field("observation", LEGACY_OBSERVATION_SCHEMA_V1),
    ),
    LEGACY_BOUND_OBSERVATION_SCHEMA_ID_V1,
)
EXACT_BOUND_OBSERVATION_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("binding", INPUT_BINDING_SCHEMA_V1),
        _field("observation", EXACT_OBSERVATION_SCHEMA_V1),
    ),
    EXACT_BOUND_OBSERVATION_SCHEMA_ID_V1,
)
OBSERVATION_PAIR_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("exact", EXACT_BOUND_OBSERVATION_SCHEMA_V1),
        _field("legacy", LEGACY_BOUND_OBSERVATION_SCHEMA_V1),
    ),
    OBSERVATION_PAIR_SCHEMA_ID_V1,
)

REFINEMENT_SCHEMA_REGISTRATIONS_V1 = (
    SchemaRegistrationV1(INPUT_BINDING_SCHEMA_ID_V1, INPUT_BINDING_SCHEMA_V1),
    SchemaRegistrationV1(LEGACY_OBSERVATION_SCHEMA_ID_V1, LEGACY_OBSERVATION_SCHEMA_V1),
    SchemaRegistrationV1(EXACT_OBSERVATION_SCHEMA_ID_V1, EXACT_OBSERVATION_SCHEMA_V1),
    SchemaRegistrationV1(
        LEGACY_BOUND_OBSERVATION_SCHEMA_ID_V1,
        LEGACY_BOUND_OBSERVATION_SCHEMA_V1,
    ),
    SchemaRegistrationV1(
        EXACT_BOUND_OBSERVATION_SCHEMA_ID_V1,
        EXACT_BOUND_OBSERVATION_SCHEMA_V1,
    ),
    SchemaRegistrationV1(OBSERVATION_PAIR_SCHEMA_ID_V1, OBSERVATION_PAIR_SCHEMA_V1),
)

REFINEMENT_ADMISSION_LIMITS_RAW_V1 = AdmissionLimitsV1(
    max_depth=MAX_REFINEMENT_DEPTH_V1,
    max_nodes=MAX_REFINEMENT_NODES_V1,
    max_canonical_bytes=MAX_REFINEMENT_BYTES_V1,
    max_collection_items=MAX_REFINEMENT_COLLECTION_ITEMS_V1,
)


@final
@dataclass(frozen=True, slots=True)
class RefinementResourceBoundsV1:
    max_bytes: int
    max_depth: int
    max_nodes: int
    max_fixtures: int
    max_observations: int
    max_collection_items: int
    max_field_utf8_bytes: int
    max_mismatch_payload_bytes: int
    max_witness_bytes: int


REFINEMENT_RESOURCE_BOUNDS_V1 = RefinementResourceBoundsV1(
    max_bytes=MAX_REFINEMENT_BYTES_V1,
    max_depth=MAX_REFINEMENT_DEPTH_V1,
    max_nodes=MAX_REFINEMENT_NODES_V1,
    max_fixtures=MAX_REFINEMENT_FIXTURES_V1,
    max_observations=MAX_REFINEMENT_OBSERVATIONS_V1,
    max_collection_items=MAX_REFINEMENT_COLLECTION_ITEMS_V1,
    max_field_utf8_bytes=MAX_REFINEMENT_FIELD_UTF8_BYTES_V1,
    max_mismatch_payload_bytes=MAX_REFINEMENT_MISMATCH_PAYLOAD_BYTES_V1,
    max_witness_bytes=MAX_REFINEMENT_WITNESS_BYTES_V1,
)


__all__ = (
    "EXACT_BOUND_OBSERVATION_SCHEMA_ID_V1",
    "EXACT_OBSERVATION_SCHEMA_ID_V1",
    "INPUT_BINDING_SCHEMA_ID_V1",
    "LEGACY_BOUND_OBSERVATION_SCHEMA_ID_V1",
    "LEGACY_OBSERVATION_SCHEMA_ID_V1",
    "MAX_REFINEMENT_BYTES_V1",
    "MAX_REFINEMENT_COLLECTION_ITEMS_V1",
    "MAX_REFINEMENT_DEPTH_V1",
    "MAX_REFINEMENT_FIELD_UTF8_BYTES_V1",
    "MAX_REFINEMENT_FIXTURES_V1",
    "MAX_REFINEMENT_MISMATCH_PAYLOAD_BYTES_V1",
    "MAX_REFINEMENT_NODES_V1",
    "MAX_REFINEMENT_OBSERVATIONS_V1",
    "MAX_REFINEMENT_WITNESS_BYTES_V1",
    "OBSERVATION_PAIR_SCHEMA_ID_V1",
    "REFINEMENT_ADMISSION_LIMITS_RAW_V1",
    "REFINEMENT_RESOURCE_BOUNDS_V1",
    "REFINEMENT_SCHEMA_REGISTRATIONS_V1",
    "REFINEMENT_SCHEMA_REVISION_V1",
    "RefinementEnumTagV1",
    "RefinementRecordTagV1",
    "RefinementResourceBoundsV1",
)
