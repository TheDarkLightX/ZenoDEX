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
    ExactBool,
    ExactInt,
    ExactKeyedMap,
    ExactProduct,
    ExactString,
    MapOf,
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
PUBLIC_STATE_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/public-state/v1"
EXECUTION_CONTEXT_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/execution-context/v1"
SETTLEMENT_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/settlement/v1"
PATCH_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/patch/v1"
EFFECTS_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/effects/v1"
REPLAY_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/replay/v1"
COMMIT_PLAN_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/commit-plan/v1"
ACCEPT_RECEIPT_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/accept-receipt/v1"
REJECT_RECEIPT_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/reject-receipt/v1"
OUTBOX_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/outbox/v1"
INTERNAL_STATE_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/internal-state/v1"
BUNDLE_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/bundle/v1"
CREATE_POOL_COMMAND_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/command/create-pool/v1"
ADD_LIQUIDITY_COMMAND_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/command/add-liquidity/v1"
REMOVE_LIQUIDITY_COMMAND_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/command/remove-liquidity/v1"
SWAP_EXACT_IN_COMMAND_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/command/swap-exact-in/v1"
SWAP_EXACT_OUT_COMMAND_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/command/swap-exact-out/v1"
ROUTE_EXACT_IN_COMMAND_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/command/route-exact-in/v1"
ROUTE_EXACT_OUT_COMMAND_SCHEMA_ID_V1 = "zenodex/fcis-m5-p4b0/command/route-exact-out/v1"

MAX_REFINEMENT_BYTES_V1 = 512_000
MAX_REFINEMENT_ARTIFACT_BYTES_V1 = 2_000_000
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
POSITIVE_V1 = ExactInt(1, MAX_REFINEMENT_SCALAR_V1)
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
PUBKEY_V1 = ExactString(
    StringRuleV1.LOWERCASE_0X_HEX,
    98,
    exact_utf8_bytes=98,
    max_characters=98,
)
EXACT_TEXT_V1 = ExactString(
    StringRuleV1.EXACT_TEXT,
    MAX_REFINEMENT_TEXT_UTF8_BYTES_V1,
    max_characters=MAX_REFINEMENT_TEXT_UTF8_BYTES_V1,
)


def _literal(value: str) -> ExactString:
    size = len(value.encode("utf-8"))
    return ExactString(
        StringRuleV1.EXACT_LITERAL,
        size,
        exact_literal=value,
        exact_utf8_bytes=size,
        max_characters=len(value),
    )


def _list_of(schema: SchemaV1, maximum: int = MAX_REFINEMENT_COLLECTION_ITEMS_V1) -> SequenceOf:
    return SequenceOf((SequenceSourceKind.EXACT_LIST,), schema, 0, maximum)


def _product(*schemas: SchemaV1) -> ExactProduct:
    return ExactProduct((SequenceSourceKind.EXACT_LIST,), schemas)


NULL_ONLY_V1 = OptionalValue(_literal("__unsupported_nonnull_p4b0_v1__"))
KEY_PAIR_V1 = _product(PUBKEY_V1, DIGEST_V1)
ENUM_TRIPLE_V1 = _product(
    _literal("zenodex/fcis-authority-state/v1"), NONNEGATIVE_V1, NONNEGATIVE_V1
)

PUBLIC_BALANCE_ENTRY_SCHEMA_V1 = ExactKeyedMap(
    (_field("amount", NONNEGATIVE_V1), _field("asset", DIGEST_V1), _field("pubkey", PUBKEY_V1)),
    "zenodex/fcis-m5-p4b0/public-balance-entry/v1",
)
PUBLIC_POOL_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("asset0", DIGEST_V1),
        _field("asset1", DIGEST_V1),
        _field("created_at", NONNEGATIVE_V1),
        _field("curve_params", EXACT_TEXT_V1),
        _field("curve_tag", SHORT_TEXT_V1),
        _field("fee_bps", NONNEGATIVE_V1),
        _field("lp_supply", NONNEGATIVE_V1),
        _field("pool_id", DIGEST_V1),
        _field("reserve0", NONNEGATIVE_V1),
        _field("reserve1", NONNEGATIVE_V1),
        _field("status", SHORT_TEXT_V1),
    ),
    "zenodex/fcis-m5-p4b0/public-pool/v1",
)
PUBLIC_LP_BALANCE_SCHEMA_V1 = ExactKeyedMap(
    (_field("amount", NONNEGATIVE_V1), _field("pool_id", DIGEST_V1), _field("pubkey", PUBKEY_V1)),
    "zenodex/fcis-m5-p4b0/public-lp-balance/v1",
)
PUBLIC_LP_RISK_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("churn_tier", NONNEGATIVE_V1),
        _field("last_churn_update_timestamp", OptionalValue(NONNEGATIVE_V1)),
        _field("last_remove_timestamp", OptionalValue(NONNEGATIVE_V1)),
        _field("pool_id", DIGEST_V1),
        _field("pubkey", PUBKEY_V1),
    ),
    "zenodex/fcis-m5-p4b0/public-lp-risk/v1",
)
PUBLIC_LP_MINT_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("last_mint_timestamp", OptionalValue(NONNEGATIVE_V1)),
        _field("pool_id", DIGEST_V1),
        _field("pubkey", PUBKEY_V1),
    ),
    "zenodex/fcis-m5-p4b0/public-lp-mint/v1",
)
PUBLIC_NONCE_SCHEMA_V1 = ExactKeyedMap(
    (_field("last_nonce", NONNEGATIVE_V1), _field("pubkey", PUBKEY_V1)),
    "zenodex/fcis-m5-p4b0/public-nonce/v1",
)
FEE_ACCUMULATOR_VALUE_SCHEMA_V1 = ExactKeyedMap(
    (_field("dust", NONNEGATIVE_V1),),
    "zenodex/fcis-m5-p4b0/fee-accumulator/v1",
)
PUBLIC_STATE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("balances", _list_of(PUBLIC_BALANCE_ENTRY_SCHEMA_V1)),
        _field("fee_accumulator", FEE_ACCUMULATOR_VALUE_SCHEMA_V1),
        _field("lp_balances", _list_of(PUBLIC_LP_BALANCE_SCHEMA_V1)),
        _field("lp_duration_risk", _list_of(PUBLIC_LP_RISK_SCHEMA_V1)),
        _field("lp_mint_timestamps", _list_of(PUBLIC_LP_MINT_SCHEMA_V1)),
        _field("nonces", _list_of(PUBLIC_NONCE_SCHEMA_V1)),
        _field("oracle", NULL_ONLY_V1),
        _field("perps", NULL_ONLY_V1),
        _field("pools", _list_of(PUBLIC_POOL_SCHEMA_V1)),
        _field("vault", NULL_ONLY_V1),
        _field("version", ExactInt(4, 4)),
    ),
    PUBLIC_STATE_SCHEMA_ID_V1,
)

FEE_SPLIT_POLICY_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("buyback_bps", NONNEGATIVE_V1),
        _field("rewards_bps", NONNEGATIVE_V1),
        _field("treasury_bps", NONNEGATIVE_V1),
    ),
    "zenodex/fcis-m5-p4b0/context/fee-split/v1",
)
LP_DURATION_POLICY_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("base_age_seconds", NONNEGATIVE_V1),
        _field("churn_window_seconds", NONNEGATIVE_V1),
        _field("decay_seconds", NONNEGATIVE_V1),
        _field("max_age_seconds", NONNEGATIVE_V1),
        _field("max_churn_tier", NONNEGATIVE_V1),
        _field("multiplier", NONNEGATIVE_V1),
    ),
    "zenodex/fcis-m5-p4b0/context/lp-duration/v1",
)
EXECUTION_CONTEXT_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("allow_cow_netting", ExactBool()),
        _field("allow_snapshot_bound_quote_bindings", ExactBool()),
        _field("fee_split_policy", OptionalValue(FEE_SPLIT_POLICY_SCHEMA_V1)),
        _field("legacy_now_authority", _literal("unavailable_at_core_step")),
        _field("lp_duration_policy", OptionalValue(LP_DURATION_POLICY_SCHEMA_V1)),
        _field("min_lp_position_age_seconds", NONNEGATIVE_V1),
        _field("now", NONNEGATIVE_V1),
        _field("protocol_fee_recipient_pubkey", OptionalValue(PUBKEY_V1)),
        _field("protocol_fee_share_bps", ExactInt(0, 10_000)),
        _field("reject_settlements_with_rejected_intents", ExactBool()),
        _field("require_all_nonces", ExactBool()),
        _field("settlement_mode", _literal("strong_proof_carrying")),
        _field("snapshot_version", ExactInt(4, 4)),
        _field("swap_ordering", _literal("greedy_ab_refined")),
    ),
    EXECUTION_CONTEXT_SCHEMA_ID_V1,
)

ROUTE_LEG_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("amount_in", NONNEGATIVE_V1),
        _field("amount_out", NONNEGATIVE_V1),
        _field("asset_in", DIGEST_V1),
        _field("asset_out", DIGEST_V1),
        _field("pool_id", DIGEST_V1),
    ),
    "zenodex/fcis-m5-p4b0/route-leg/v1",
)
ROUTE_FINGERPRINTS_SCHEMA_V1 = MapOf(
    DIGEST_V1,
    DIGEST_V1,
    64,
    "zenodex/fcis-m5-p4b0/route-fingerprints/v1",
)


def _command_schema(
    schema_id: str,
    kind: str,
    field_schema: SchemaV1,
) -> ExactKeyedMap:
    return ExactKeyedMap(
        (
            _field("deadline", NONNEGATIVE_V1),
            _field("fields", field_schema),
            _field("intent_id", DIGEST_V1),
            _field("kind", _literal(kind)),
            _field("module", _literal("TauSwap")),
            _field("sender_pubkey", PUBKEY_V1),
            _field("version", _literal("0.1")),
        ),
        schema_id,
    )


CREATE_POOL_FIELDS_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("amount0", NONNEGATIVE_V1),
        _field("amount1", NONNEGATIVE_V1),
        _field("asset0", DIGEST_V1),
        _field("asset1", DIGEST_V1),
        _field("fee_bps", NONNEGATIVE_V1),
        _field("nonce", NONNEGATIVE_V1),
    ),
    "zenodex/fcis-m5-p4b0/command-fields/create-pool/v1",
)
ADD_LIQUIDITY_FIELDS_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("amount0_desired", NONNEGATIVE_V1),
        _field("amount0_min", NONNEGATIVE_V1),
        _field("amount1_desired", NONNEGATIVE_V1),
        _field("amount1_min", NONNEGATIVE_V1),
        _field("nonce", NONNEGATIVE_V1),
        _field("pool_id", DIGEST_V1),
    ),
    "zenodex/fcis-m5-p4b0/command-fields/add-liquidity/v1",
)
REMOVE_LIQUIDITY_FIELDS_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("amount0_min", NONNEGATIVE_V1),
        _field("amount1_min", NONNEGATIVE_V1),
        _field("lp_amount", NONNEGATIVE_V1),
        _field("nonce", NONNEGATIVE_V1),
        _field("pool_id", DIGEST_V1),
    ),
    "zenodex/fcis-m5-p4b0/command-fields/remove-liquidity/v1",
)
SWAP_EXACT_IN_FIELDS_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("amount_in", NONNEGATIVE_V1),
        _field("asset_in", DIGEST_V1),
        _field("asset_out", DIGEST_V1),
        _field("min_amount_out", NONNEGATIVE_V1),
        _field("nonce", NONNEGATIVE_V1),
        _field("pool_id", DIGEST_V1),
        _field("recipient", PUBKEY_V1),
    ),
    "zenodex/fcis-m5-p4b0/command-fields/swap-exact-in/v1",
    required_field_names=("amount_in", "asset_in", "asset_out", "min_amount_out", "pool_id"),
)
SWAP_EXACT_OUT_FIELDS_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("amount_out", NONNEGATIVE_V1),
        _field("asset_in", DIGEST_V1),
        _field("asset_out", DIGEST_V1),
        _field("max_amount_in", NONNEGATIVE_V1),
        _field("nonce", NONNEGATIVE_V1),
        _field("pool_id", DIGEST_V1),
        _field("recipient", PUBKEY_V1),
    ),
    "zenodex/fcis-m5-p4b0/command-fields/swap-exact-out/v1",
    required_field_names=("amount_out", "asset_in", "asset_out", "max_amount_in", "pool_id"),
)
ROUTE_EXACT_IN_FIELDS_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("asset_in", DIGEST_V1),
        _field("asset_out", DIGEST_V1),
        _field("leg_indices", _list_of(NONNEGATIVE_V1, 64)),
        _field("nonce", NONNEGATIVE_V1),
        _field("recipient", PUBKEY_V1),
        _field("route_legs", _list_of(ROUTE_LEG_SCHEMA_V1, 64)),
        _field("route_pool_fingerprints", ROUTE_FINGERPRINTS_SCHEMA_V1),
        _field("total_amount_in", NONNEGATIVE_V1),
        _field("total_min_amount_out", NONNEGATIVE_V1),
    ),
    "zenodex/fcis-m5-p4b0/command-fields/route-exact-in/v1",
)
ROUTE_EXACT_OUT_FIELDS_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("asset_in", DIGEST_V1),
        _field("asset_out", DIGEST_V1),
        _field("leg_indices", _list_of(NONNEGATIVE_V1, 64)),
        _field("nonce", NONNEGATIVE_V1),
        _field("recipient", PUBKEY_V1),
        _field("route_legs", _list_of(ROUTE_LEG_SCHEMA_V1, 64)),
        _field("route_pool_fingerprints", ROUTE_FINGERPRINTS_SCHEMA_V1),
        _field("total_amount_out", NONNEGATIVE_V1),
        _field("total_max_amount_in", NONNEGATIVE_V1),
    ),
    "zenodex/fcis-m5-p4b0/command-fields/route-exact-out/v1",
)
CREATE_POOL_COMMAND_SCHEMA_V1 = _command_schema(
    CREATE_POOL_COMMAND_SCHEMA_ID_V1, "CREATE_POOL", CREATE_POOL_FIELDS_SCHEMA_V1
)
ADD_LIQUIDITY_COMMAND_SCHEMA_V1 = _command_schema(
    ADD_LIQUIDITY_COMMAND_SCHEMA_ID_V1, "ADD_LIQUIDITY", ADD_LIQUIDITY_FIELDS_SCHEMA_V1
)
REMOVE_LIQUIDITY_COMMAND_SCHEMA_V1 = _command_schema(
    REMOVE_LIQUIDITY_COMMAND_SCHEMA_ID_V1,
    "REMOVE_LIQUIDITY",
    REMOVE_LIQUIDITY_FIELDS_SCHEMA_V1,
)
SWAP_EXACT_IN_COMMAND_SCHEMA_V1 = _command_schema(
    SWAP_EXACT_IN_COMMAND_SCHEMA_ID_V1, "SWAP_EXACT_IN", SWAP_EXACT_IN_FIELDS_SCHEMA_V1
)
SWAP_EXACT_OUT_COMMAND_SCHEMA_V1 = _command_schema(
    SWAP_EXACT_OUT_COMMAND_SCHEMA_ID_V1, "SWAP_EXACT_OUT", SWAP_EXACT_OUT_FIELDS_SCHEMA_V1
)
ROUTE_EXACT_IN_COMMAND_SCHEMA_V1 = _command_schema(
    ROUTE_EXACT_IN_COMMAND_SCHEMA_ID_V1, "ROUTE_EXACT_IN", ROUTE_EXACT_IN_FIELDS_SCHEMA_V1
)
ROUTE_EXACT_OUT_COMMAND_SCHEMA_V1 = _command_schema(
    ROUTE_EXACT_OUT_COMMAND_SCHEMA_ID_V1, "ROUTE_EXACT_OUT", ROUTE_EXACT_OUT_FIELDS_SCHEMA_V1
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

BALANCE_DELTA_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("asset", DIGEST_V1),
        _field("delta_add", NONNEGATIVE_V1),
        _field("delta_sub", NONNEGATIVE_V1),
        _field("pubkey", PUBKEY_V1),
    ),
    "zenodex/fcis-m5-p4b0/settlement/balance-delta/v1",
)
RESERVE_DELTA_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("asset", DIGEST_V1),
        _field("delta_add", NONNEGATIVE_V1),
        _field("delta_sub", NONNEGATIVE_V1),
        _field("pool_id", DIGEST_V1),
    ),
    "zenodex/fcis-m5-p4b0/settlement/reserve-delta/v1",
)
LP_DELTA_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("delta_add", NONNEGATIVE_V1),
        _field("delta_sub", NONNEGATIVE_V1),
        _field("pool_id", DIGEST_V1),
        _field("pubkey", PUBKEY_V1),
    ),
    "zenodex/fcis-m5-p4b0/settlement/lp-delta/v1",
)
FILL_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("action", SHORT_TEXT_V1),
        _field("amount0_out", OptionalValue(NONNEGATIVE_V1)),
        _field("amount0_used", OptionalValue(NONNEGATIVE_V1)),
        _field("amount1_out", OptionalValue(NONNEGATIVE_V1)),
        _field("amount1_used", OptionalValue(NONNEGATIVE_V1)),
        _field("amount_in_filled", OptionalValue(NONNEGATIVE_V1)),
        _field("amount_out_filled", OptionalValue(NONNEGATIVE_V1)),
        _field("fee_paid", OptionalValue(NONNEGATIVE_V1)),
        _field("intent_id", DIGEST_V1),
        _field("lp_burned", OptionalValue(NONNEGATIVE_V1)),
        _field("lp_minted", OptionalValue(NONNEGATIVE_V1)),
        _field("protocol_fee_paid", OptionalValue(NONNEGATIVE_V1)),
        _field("reason", OptionalValue(EXACT_TEXT_V1)),
        _field("reserve_in_before", OptionalValue(NONNEGATIVE_V1)),
        _field("reserve_out_before", OptionalValue(NONNEGATIVE_V1)),
    ),
    "zenodex/fcis-m5-p4b0/settlement/fill/v1",
)
SETTLEMENT_EVENT_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("asset0", DIGEST_V1),
        _field("asset1", DIGEST_V1),
        _field("created_at", NONNEGATIVE_V1),
        _field("curve_params", EXACT_TEXT_V1),
        _field("curve_tag", SHORT_TEXT_V1),
        _field("fee_bps", NONNEGATIVE_V1),
        _field("pool_id", DIGEST_V1),
        _field("status", SHORT_TEXT_V1),
        _field("type", SHORT_TEXT_V1),
    ),
    "zenodex/fcis-m5-p4b0/settlement/event/v1",
)
INCLUDED_INTENT_SCHEMA_V1 = _product(DIGEST_V1, SHORT_TEXT_V1)
SETTLEMENT_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("balance_deltas", _list_of(BALANCE_DELTA_SCHEMA_V1)),
        _field("batch_ref", EXACT_TEXT_V1),
        _field("events", _list_of(SETTLEMENT_EVENT_SCHEMA_V1)),
        _field("fills", _list_of(FILL_SCHEMA_V1)),
        _field("included_intents", _list_of(INCLUDED_INTENT_SCHEMA_V1)),
        _field("lp_deltas", _list_of(LP_DELTA_SCHEMA_V1)),
        _field("module", _literal("TauSwap")),
        _field("reserve_deltas", _list_of(RESERVE_DELTA_SCHEMA_V1)),
        _field("version", _literal("0.1")),
    ),
    SETTLEMENT_SCHEMA_ID_V1,
    required_field_names=(
        "balance_deltas",
        "batch_ref",
        "fills",
        "included_intents",
        "lp_deltas",
        "module",
        "reserve_deltas",
        "version",
    ),
)

INTERNAL_POOL_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("asset0", DIGEST_V1),
        _field("asset1", DIGEST_V1),
        _field("created_at", NONNEGATIVE_V1),
        _field("curve_params", EXACT_TEXT_V1),
        _field("curve_tag", SHORT_TEXT_V1),
        _field("fee_bps", NONNEGATIVE_V1),
        _field("lp_supply", NONNEGATIVE_V1),
        _field("pool_id", DIGEST_V1),
        _field("reserve0", NONNEGATIVE_V1),
        _field("reserve1", NONNEGATIVE_V1),
        _field("status", ENUM_TRIPLE_V1),
    ),
    "zenodex/fcis-m5-p4b0/internal-pool/v1",
)
LP_POSITION_VALUE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("balance", NONNEGATIVE_V1),
        _field("churn_tier", NONNEGATIVE_V1),
        _field("last_churn_update_timestamp", OptionalValue(NONNEGATIVE_V1)),
        _field("last_mint_timestamp", OptionalValue(NONNEGATIVE_V1)),
        _field("last_remove_timestamp", OptionalValue(NONNEGATIVE_V1)),
    ),
    "zenodex/fcis-m5-p4b0/lp-position-value/v1",
)
BALANCE_WRITE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("expected_old", NONNEGATIVE_V1),
        _field("key", KEY_PAIR_V1),
        _field("replacement", OptionalValue(POSITIVE_V1)),
    ),
    "zenodex/fcis-m5-p4b0/patch/balance-write/v1",
)
POOL_WRITE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("expected", OptionalValue(INTERNAL_POOL_SCHEMA_V1)),
        _field("pool_id", DIGEST_V1),
        _field("replacement", OptionalValue(INTERNAL_POOL_SCHEMA_V1)),
    ),
    "zenodex/fcis-m5-p4b0/patch/pool-write/v1",
)
LP_WRITE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("expected", LP_POSITION_VALUE_SCHEMA_V1),
        _field("key", KEY_PAIR_V1),
        _field("replacement", LP_POSITION_VALUE_SCHEMA_V1),
    ),
    "zenodex/fcis-m5-p4b0/patch/lp-write/v1",
)
FEE_WRITE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("expected", FEE_ACCUMULATOR_VALUE_SCHEMA_V1),
        _field("replacement", FEE_ACCUMULATOR_VALUE_SCHEMA_V1),
    ),
    "zenodex/fcis-m5-p4b0/patch/fee-write/v1",
)
PATCH_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("balance_writes", _list_of(BALANCE_WRITE_SCHEMA_V1)),
        _field("fee_accumulator_write", OptionalValue(FEE_WRITE_SCHEMA_V1)),
        _field("lp_writes", _list_of(LP_WRITE_SCHEMA_V1)),
        _field("oracle_write", NULL_ONLY_V1),
        _field("perps_write", NULL_ONLY_V1),
        _field("pool_writes", _list_of(POOL_WRITE_SCHEMA_V1)),
        _field("vault_write", NULL_ONLY_V1),
    ),
    PATCH_SCHEMA_ID_V1,
)
EFFECTS_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("fee_allocation", OptionalValue(FEE_ALLOCATION_SCHEMA_V1)),
        _field("settlement", SETTLEMENT_SCHEMA_V1),
        _field("total_swap_fees", NONNEGATIVE_V1),
    ),
    EFFECTS_SCHEMA_ID_V1,
)
NONCE_ADVANCE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("expected_last", NONNEGATIVE_V1),
        _field("new_last", POSITIVE_V1),
        _field("pubkey", PUBKEY_V1),
    ),
    "zenodex/fcis-m5-p4b0/replay/nonce-advance/v1",
)
NULLIFIER_SCHEMA_V1 = ExactKeyedMap(
    (_field("intent_id", DIGEST_V1), _field("pubkey", PUBKEY_V1)),
    "zenodex/fcis-m5-p4b0/replay/nullifier/v1",
)
REPLAY_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("nonce_advances", _list_of(NONCE_ADVANCE_SCHEMA_V1)),
        _field("nullifiers", _list_of(NULLIFIER_SCHEMA_V1)),
    ),
    REPLAY_SCHEMA_ID_V1,
)
COMMIT_PLAN_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("effects", EFFECTS_SCHEMA_V1),
        _field("patch", PATCH_SCHEMA_V1),
        _field("replay", REPLAY_SCHEMA_V1),
    ),
    COMMIT_PLAN_SCHEMA_ID_V1,
)

RECEIPT_BINDING_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("algorithm_id", _literal("zenodex/fcis/spot-step-evaluator/v1")),
        _field("algorithm_version", ExactInt(1, 1)),
        _field("budget_hash", DIGEST_V1),
        _field("codec_version", ExactInt(1, 1)),
        _field("command_or_batch_root", DIGEST_V1),
        _field("commit_plan_root", DIGEST_V1),
        _field("execution_context_hash", DIGEST_V1),
        _field("next_state_root", DIGEST_V1),
        _field("patch_root", DIGEST_V1),
        _field("pre_state_root", DIGEST_V1),
        _field("schema_version", ExactInt(1, 1)),
        _field("snapshot_commitment", DIGEST_V1),
        _field("snapshot_version", ExactInt(4, 4)),
        _field("support_root", DIGEST_V1),
        _field("support_root_version", ExactInt(5, 5)),
        _field("support_set_commitment", DIGEST_V1),
    ),
    "zenodex/fcis-m5-p4b0/receipt-binding/v1",
)
ACCEPT_RECEIPT_SCHEMA_V1 = ExactKeyedMap(
    (_field("binding", RECEIPT_BINDING_SCHEMA_V1),),
    ACCEPT_RECEIPT_SCHEMA_ID_V1,
)
REJECT_RECEIPT_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("algorithm_id", _literal("zenodex/fcis/spot-step-evaluator/v1")),
        _field("algorithm_version", ExactInt(1, 1)),
        _field("budget_hash", DIGEST_V1),
        _field("code", ENUM_TRIPLE_V1),
        _field("codec_version", ExactInt(1, 1)),
        _field("command_or_batch_root", DIGEST_V1),
        _field("execution_context_hash", DIGEST_V1),
        _field("path", _list_of(SHORT_TEXT_V1, 64)),
        _field("phase", ENUM_TRIPLE_V1),
        _field("pre_state_root", DIGEST_V1),
        _field("public_reason", TEXT_V1),
        _field("schema_version", ExactInt(1, 1)),
    ),
    REJECT_RECEIPT_SCHEMA_ID_V1,
)


def _payload_entry(name: str, schema: SchemaV1) -> ExactProduct:
    return _product(_literal(name), schema)


CREATE_POOL_PAYLOAD_SCHEMA_V1 = _product(
    _payload_entry("asset0", DIGEST_V1),
    _payload_entry("asset1", DIGEST_V1),
    _payload_entry("created_at", NONNEGATIVE_V1),
    _payload_entry("curve_params", EXACT_TEXT_V1),
    _payload_entry("curve_tag", SHORT_TEXT_V1),
    _payload_entry("fee_bps", NONNEGATIVE_V1),
    _payload_entry("pool_id", DIGEST_V1),
    _payload_entry("status", SHORT_TEXT_V1),
    _payload_entry("type", _literal("CREATE_POOL")),
)
OUTBOX_RECORD_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("effect_identity", DIGEST_V1),
        _field("effect_index", NONNEGATIVE_V1),
        _field("effect_kind", ENUM_TRIPLE_V1),
        _field("idempotency_key", DIGEST_V1),
        _field("payload", CREATE_POOL_PAYLOAD_SCHEMA_V1),
    ),
    "zenodex/fcis-m5-p4b0/outbox/record/v1",
)
OUTBOX_SCHEMA_V1 = ExactKeyedMap(
    (_field("records", _list_of(OUTBOX_RECORD_SCHEMA_V1)),),
    OUTBOX_SCHEMA_ID_V1,
)

INTERNAL_BALANCE_TABLE_SCHEMA_V1 = ExactKeyedMap(
    (_field("_balances", _list_of(_product(KEY_PAIR_V1, NONNEGATIVE_V1))),),
    "zenodex/fcis-m5-p4b0/internal-balance-table/v1",
)
INTERNAL_LP_TABLE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("_balances", _list_of(_product(KEY_PAIR_V1, NONNEGATIVE_V1))),
        _field("_churn_tiers", _list_of(_product(KEY_PAIR_V1, NONNEGATIVE_V1))),
        _field(
            "_last_churn_update_timestamps",
            _list_of(_product(KEY_PAIR_V1, NONNEGATIVE_V1)),
        ),
        _field("_last_mint_timestamps", _list_of(_product(KEY_PAIR_V1, NONNEGATIVE_V1))),
        _field("_last_remove_timestamps", _list_of(_product(KEY_PAIR_V1, NONNEGATIVE_V1))),
    ),
    "zenodex/fcis-m5-p4b0/internal-lp-table/v1",
)
INTERNAL_NONCE_TABLE_SCHEMA_V1 = ExactKeyedMap(
    (_field("_last", _list_of(_product(PUBKEY_V1, NONNEGATIVE_V1))),),
    "zenodex/fcis-m5-p4b0/internal-nonce-table/v1",
)
INTERNAL_STATE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("balances", INTERNAL_BALANCE_TABLE_SCHEMA_V1),
        _field("fee_accumulator", FEE_ACCUMULATOR_VALUE_SCHEMA_V1),
        _field("lp_balances", INTERNAL_LP_TABLE_SCHEMA_V1),
        _field("nonces", INTERNAL_NONCE_TABLE_SCHEMA_V1),
        _field("oracle", NULL_ONLY_V1),
        _field("perps", NULL_ONLY_V1),
        _field("pools", _list_of(_product(DIGEST_V1, INTERNAL_POOL_SCHEMA_V1))),
        _field("vault", NULL_ONLY_V1),
    ),
    INTERNAL_STATE_SCHEMA_ID_V1,
)
ACCEPT_DECISION_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("commit_plan", COMMIT_PLAN_SCHEMA_V1),
        _field("next_state", INTERNAL_STATE_SCHEMA_V1),
        _field("receipt", ACCEPT_RECEIPT_SCHEMA_V1),
    ),
    "zenodex/fcis-m5-p4b0/accept-decision/v1",
)
BUNDLE_SCHEMA_V1 = ExactKeyedMap(
    (
        _field("decision", ACCEPT_DECISION_SCHEMA_V1),
        _field("expected_pre_root", DIGEST_V1),
        _field("outbox_plan", OUTBOX_SCHEMA_V1),
        _field("receipt_root", DIGEST_V1),
    ),
    BUNDLE_SCHEMA_ID_V1,
)


class RefinementComponentKindV1(Enum):
    PUBLIC_STATE = PUBLIC_STATE_SCHEMA_ID_V1
    EXECUTION_CONTEXT = EXECUTION_CONTEXT_SCHEMA_ID_V1
    SETTLEMENT = SETTLEMENT_SCHEMA_ID_V1
    PATCH = PATCH_SCHEMA_ID_V1
    EFFECTS = EFFECTS_SCHEMA_ID_V1
    REPLAY = REPLAY_SCHEMA_ID_V1
    COMMIT_PLAN = COMMIT_PLAN_SCHEMA_ID_V1
    ACCEPT_RECEIPT = ACCEPT_RECEIPT_SCHEMA_ID_V1
    REJECT_RECEIPT = REJECT_RECEIPT_SCHEMA_ID_V1
    OUTBOX = OUTBOX_SCHEMA_ID_V1
    INTERNAL_STATE = INTERNAL_STATE_SCHEMA_ID_V1
    BUNDLE = BUNDLE_SCHEMA_ID_V1


def command_schema_id_v1(command_kind: str) -> str | None:
    if command_kind == "CREATE_POOL":
        return CREATE_POOL_COMMAND_SCHEMA_ID_V1
    if command_kind == "ADD_LIQUIDITY":
        return ADD_LIQUIDITY_COMMAND_SCHEMA_ID_V1
    if command_kind == "REMOVE_LIQUIDITY":
        return REMOVE_LIQUIDITY_COMMAND_SCHEMA_ID_V1
    if command_kind == "SWAP_EXACT_IN":
        return SWAP_EXACT_IN_COMMAND_SCHEMA_ID_V1
    if command_kind == "SWAP_EXACT_OUT":
        return SWAP_EXACT_OUT_COMMAND_SCHEMA_ID_V1
    if command_kind == "ROUTE_EXACT_IN":
        return ROUTE_EXACT_IN_COMMAND_SCHEMA_ID_V1
    if command_kind == "ROUTE_EXACT_OUT":
        return ROUTE_EXACT_OUT_COMMAND_SCHEMA_ID_V1
    return None


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
    SchemaRegistrationV1(PUBLIC_STATE_SCHEMA_ID_V1, PUBLIC_STATE_SCHEMA_V1),
    SchemaRegistrationV1(EXECUTION_CONTEXT_SCHEMA_ID_V1, EXECUTION_CONTEXT_SCHEMA_V1),
    SchemaRegistrationV1(SETTLEMENT_SCHEMA_ID_V1, SETTLEMENT_SCHEMA_V1),
    SchemaRegistrationV1(PATCH_SCHEMA_ID_V1, PATCH_SCHEMA_V1),
    SchemaRegistrationV1(EFFECTS_SCHEMA_ID_V1, EFFECTS_SCHEMA_V1),
    SchemaRegistrationV1(REPLAY_SCHEMA_ID_V1, REPLAY_SCHEMA_V1),
    SchemaRegistrationV1(COMMIT_PLAN_SCHEMA_ID_V1, COMMIT_PLAN_SCHEMA_V1),
    SchemaRegistrationV1(ACCEPT_RECEIPT_SCHEMA_ID_V1, ACCEPT_RECEIPT_SCHEMA_V1),
    SchemaRegistrationV1(REJECT_RECEIPT_SCHEMA_ID_V1, REJECT_RECEIPT_SCHEMA_V1),
    SchemaRegistrationV1(OUTBOX_SCHEMA_ID_V1, OUTBOX_SCHEMA_V1),
    SchemaRegistrationV1(INTERNAL_STATE_SCHEMA_ID_V1, INTERNAL_STATE_SCHEMA_V1),
    SchemaRegistrationV1(BUNDLE_SCHEMA_ID_V1, BUNDLE_SCHEMA_V1),
    SchemaRegistrationV1(CREATE_POOL_COMMAND_SCHEMA_ID_V1, CREATE_POOL_COMMAND_SCHEMA_V1),
    SchemaRegistrationV1(
        ADD_LIQUIDITY_COMMAND_SCHEMA_ID_V1,
        ADD_LIQUIDITY_COMMAND_SCHEMA_V1,
    ),
    SchemaRegistrationV1(
        REMOVE_LIQUIDITY_COMMAND_SCHEMA_ID_V1,
        REMOVE_LIQUIDITY_COMMAND_SCHEMA_V1,
    ),
    SchemaRegistrationV1(SWAP_EXACT_IN_COMMAND_SCHEMA_ID_V1, SWAP_EXACT_IN_COMMAND_SCHEMA_V1),
    SchemaRegistrationV1(
        SWAP_EXACT_OUT_COMMAND_SCHEMA_ID_V1,
        SWAP_EXACT_OUT_COMMAND_SCHEMA_V1,
    ),
    SchemaRegistrationV1(
        ROUTE_EXACT_IN_COMMAND_SCHEMA_ID_V1,
        ROUTE_EXACT_IN_COMMAND_SCHEMA_V1,
    ),
    SchemaRegistrationV1(
        ROUTE_EXACT_OUT_COMMAND_SCHEMA_ID_V1,
        ROUTE_EXACT_OUT_COMMAND_SCHEMA_V1,
    ),
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
    "ACCEPT_RECEIPT_SCHEMA_ID_V1",
    "BUNDLE_SCHEMA_ID_V1",
    "COMMIT_PLAN_SCHEMA_ID_V1",
    "EFFECTS_SCHEMA_ID_V1",
    "EXECUTION_CONTEXT_SCHEMA_ID_V1",
    "EXACT_BOUND_OBSERVATION_SCHEMA_ID_V1",
    "EXACT_OBSERVATION_SCHEMA_ID_V1",
    "INPUT_BINDING_SCHEMA_ID_V1",
    "LEGACY_BOUND_OBSERVATION_SCHEMA_ID_V1",
    "LEGACY_OBSERVATION_SCHEMA_ID_V1",
    "MAX_REFINEMENT_BYTES_V1",
    "MAX_REFINEMENT_ARTIFACT_BYTES_V1",
    "MAX_REFINEMENT_COLLECTION_ITEMS_V1",
    "MAX_REFINEMENT_DEPTH_V1",
    "MAX_REFINEMENT_FIELD_UTF8_BYTES_V1",
    "MAX_REFINEMENT_FIXTURES_V1",
    "MAX_REFINEMENT_MISMATCH_PAYLOAD_BYTES_V1",
    "MAX_REFINEMENT_NODES_V1",
    "MAX_REFINEMENT_OBSERVATIONS_V1",
    "MAX_REFINEMENT_WITNESS_BYTES_V1",
    "OBSERVATION_PAIR_SCHEMA_ID_V1",
    "OUTBOX_SCHEMA_ID_V1",
    "PATCH_SCHEMA_ID_V1",
    "PUBLIC_STATE_SCHEMA_ID_V1",
    "REFINEMENT_ADMISSION_LIMITS_RAW_V1",
    "REFINEMENT_RESOURCE_BOUNDS_V1",
    "REFINEMENT_SCHEMA_REGISTRATIONS_V1",
    "REFINEMENT_SCHEMA_REVISION_V1",
    "REJECT_RECEIPT_SCHEMA_ID_V1",
    "REPLAY_SCHEMA_ID_V1",
    "SETTLEMENT_SCHEMA_ID_V1",
    "INTERNAL_STATE_SCHEMA_ID_V1",
    "RefinementComponentKindV1",
    "RefinementEnumTagV1",
    "RefinementRecordTagV1",
    "RefinementResourceBoundsV1",
    "command_schema_id_v1",
)
