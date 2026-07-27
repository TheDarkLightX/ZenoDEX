"""Closed kind-indexed schema and shared field registry for DEX intents."""

from __future__ import annotations

from typing import cast

from ..core.domain_limits import (
    DEX_LP_AMOUNT_MAX,
    DEX_LP_SUPPLY_MAX,
    DEX_POOL_RESERVE_MAX,
    DEX_SWAP_AMOUNT_MAX,
)
from .fcis_route_binding_schema import (
    ROUTE_LEGS_SCHEMA_V1,
    ROUTE_POOL_FINGERPRINTS_SCHEMA_V1,
)
from .intent_field_registry import (
    intent_allowed_field_names_v1,
    intent_required_field_names_v1,
)
from .intent_snapshots import OwnedIntentV1
from .intents import (
    CreatePoolIntent,
    Intent,
    IntentKind,
    RouteIntent,
    SwapIntent,
    ValidatedIntent,
)
from .owned_collections import OwnedEnumV1, OwnedMapV1
from .owned_json import JSON_OBJECT_SCHEMA_V1, OwnedJsonValueV1
from .pools import normalize_curve_config, normalize_pool_asset_pair
from .snapshot_combinators import (
    DeclaredFieldV1,
    EnumRegistrationV1,
    ExactEnum,
    ExactInt,
    ExactKeyedMap,
    ExactString,
    OptionalValue,
    RecordRegistrationV1,
    SchemaRegistrationV1,
    SchemaV1,
    SequenceOf,
    SequenceSourceKind,
    StringRuleV1,
    TaggedRecordOf,
    TaggedVariantV1,
)
from .state_snapshot_schema import (
    StateEnumTagV1,
    StateRecordTagV1,
    state_enum_tag_ordinal_v1,
)

INTENT_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/authority/intent/v1"
INTENT_BATCH_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/authority/intent-batch/v1"


def _field(name: str, schema: SchemaV1) -> DeclaredFieldV1:
    return DeclaredFieldV1(name, schema)


TEXT_256_V1 = ExactString(StringRuleV1.NON_EMPTY, 1_024, max_characters=256)
TEXT_512_V1 = ExactString(StringRuleV1.NON_EMPTY, 2_048, max_characters=512)
TEXT_4096_V1 = ExactString(StringRuleV1.NON_EMPTY, 16_384, max_characters=4_096)
EXACT_TEXT_4096_V1 = ExactString(StringRuleV1.EXACT_TEXT, 16_384, max_characters=4_096)
INTENT_ID_V1 = ExactString(
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
HASH_32_V1 = INTENT_ID_V1
LEG_INDICES_V1 = SequenceOf(
    (SequenceSourceKind.EXACT_LIST, SequenceSourceKind.EXACT_TUPLE),
    ExactInt(0, None),
    1,
    256,
)

_FIELD_SCHEMAS_V1: tuple[tuple[str, SchemaV1], ...] = (
    ("nonce", ExactInt(1, 0xFFFF_FFFF)),
    ("recipient", TEXT_512_V1),
    ("submission_order", ExactInt(0, None)),
    ("quote_receipt_hash", HASH_32_V1),
    ("quote_pool_fingerprint", TEXT_512_V1),
    ("quote_receipt_leg_index", ExactInt(0, None)),
    ("oracle_authorization", JSON_OBJECT_SCHEMA_V1),
    ("pool_id", TEXT_256_V1),
    ("asset_in", TEXT_256_V1),
    ("asset_out", TEXT_256_V1),
    ("amount_in", ExactInt(1, DEX_SWAP_AMOUNT_MAX)),
    ("min_amount_out", ExactInt(0, DEX_SWAP_AMOUNT_MAX)),
    ("amount_out", ExactInt(1, DEX_SWAP_AMOUNT_MAX)),
    ("max_amount_in", ExactInt(1, DEX_SWAP_AMOUNT_MAX)),
    ("asset0", TEXT_256_V1),
    ("asset1", TEXT_256_V1),
    ("fee_bps", ExactInt(0, 10_000)),
    ("amount0", ExactInt(1, DEX_LP_AMOUNT_MAX)),
    ("amount1", ExactInt(1, DEX_LP_AMOUNT_MAX)),
    ("created_at", ExactInt(0, None)),
    ("curve_tag", TEXT_256_V1),
    ("curve_params", EXACT_TEXT_4096_V1),
    ("amount0_desired", ExactInt(1, DEX_LP_AMOUNT_MAX)),
    ("amount1_desired", ExactInt(1, DEX_LP_AMOUNT_MAX)),
    ("lp_amount", ExactInt(1, DEX_LP_SUPPLY_MAX)),
    ("leg_indices", LEG_INDICES_V1),
    ("total_amount_in", ExactInt(1, DEX_SWAP_AMOUNT_MAX)),
    ("total_min_amount_out", ExactInt(0, DEX_SWAP_AMOUNT_MAX)),
    ("total_amount_out", ExactInt(1, DEX_SWAP_AMOUNT_MAX)),
    ("total_max_amount_in", ExactInt(0, DEX_SWAP_AMOUNT_MAX)),
    ("route_legs", ROUTE_LEGS_SCHEMA_V1),
    ("route_pool_fingerprints", ROUTE_POOL_FINGERPRINTS_SCHEMA_V1),
)

_KIND_FIELD_SCHEMA_OVERRIDES_V1: tuple[tuple[IntentKind, str, SchemaV1], ...] = (
    (IntentKind.ADD_LIQUIDITY, "amount0_min", ExactInt(0, DEX_LP_AMOUNT_MAX)),
    (IntentKind.ADD_LIQUIDITY, "amount1_min", ExactInt(0, DEX_LP_AMOUNT_MAX)),
    (IntentKind.REMOVE_LIQUIDITY, "amount0_min", ExactInt(0, DEX_POOL_RESERVE_MAX)),
    (IntentKind.REMOVE_LIQUIDITY, "amount1_min", ExactInt(0, DEX_POOL_RESERVE_MAX)),
)


def _field_schema(kind: IntentKind, name: str) -> SchemaV1:
    for registered_kind, registered_name, schema in _KIND_FIELD_SCHEMA_OVERRIDES_V1:
        if registered_kind is kind and registered_name == name:
            return schema
    for registered_name, schema in _FIELD_SCHEMAS_V1:
        if registered_name == name:
            return schema
    raise ValueError("intent field schema registry drift")


def _field_map_schema(kind: IntentKind) -> ExactKeyedMap:
    allowed = intent_allowed_field_names_v1(kind)
    required = intent_required_field_names_v1(kind)
    return ExactKeyedMap(
        tuple(_field(name, _field_schema(kind, name)) for name in allowed),
        f"zenodex/fcis/authority/intent-fields/{kind.value.lower()}/v1",
        required,
    )


def _intent_variant(kind: IntentKind) -> TaggedVariantV1:
    return TaggedVariantV1(
        kind,
        (
            _field(
                "module",
                ExactString(
                    StringRuleV1.EXACT_LITERAL,
                    7,
                    exact_literal="TauSwap",
                    exact_utf8_bytes=7,
                ),
            ),
            _field(
                "version",
                ExactString(
                    StringRuleV1.EXACT_LITERAL,
                    3,
                    exact_literal="0.1",
                    exact_utf8_bytes=3,
                ),
            ),
            _field("kind", ExactEnum(StateEnumTagV1.INTENT_KIND)),
            _field("intent_id", INTENT_ID_V1),
            _field("sender_pubkey", PUBKEY_V1),
            _field("deadline", ExactInt(0, None)),
            _field("salt", OptionalValue(TEXT_4096_V1)),
            _field("fields", _field_map_schema(kind)),
        ),
    )


INTENT_SCHEMA_V1 = TaggedRecordOf(
    StateRecordTagV1.INTENT,
    "kind",
    StateEnumTagV1.INTENT_KIND,
    tuple(_intent_variant(kind) for kind in IntentKind),
)
INTENT_BATCH_SCHEMA_V1 = SequenceOf(
    (SequenceSourceKind.EXACT_LIST, SequenceSourceKind.EXACT_TUPLE),
    INTENT_SCHEMA_V1,
    0,
    256,
)

INTENT_ENUM_REGISTRATIONS_V1 = (EnumRegistrationV1(StateEnumTagV1.INTENT_KIND, IntentKind),)
INTENT_RECORD_REGISTRATIONS_V1 = (
    RecordRegistrationV1(
        StateRecordTagV1.INTENT,
        Intent,
        OwnedIntentV1,
        additional_source_types=(
            SwapIntent,
            RouteIntent,
            CreatePoolIntent,
            ValidatedIntent,
        ),
    ),
)
INTENT_SCHEMA_REGISTRATIONS_V1 = (
    SchemaRegistrationV1(INTENT_ADMISSION_SCHEMA_ID_V1, INTENT_SCHEMA_V1),
    SchemaRegistrationV1(INTENT_BATCH_ADMISSION_SCHEMA_ID_V1, INTENT_BATCH_SCHEMA_V1),
)


def intent_kind_text_v1(kind: OwnedEnumV1) -> str:
    from .state_snapshot_values import FCIS_STATE_SCHEMA_REVISION_V1

    if (
        type(kind) is not OwnedEnumV1
        or kind.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or kind.enum_tag_ordinal != state_enum_tag_ordinal_v1(StateEnumTagV1.INTENT_KIND)
        or not 0 <= kind.member_ordinal < len(tuple(IntentKind))
    ):
        raise TypeError("owned intent kind metadata mismatch")
    return tuple(IntentKind)[kind.member_ordinal].value


def _owned_field_map(intent: OwnedIntentV1) -> OwnedMapV1[str, OwnedJsonValueV1]:
    fields = intent.fields
    if type(fields) is not OwnedMapV1:
        raise TypeError("owned intent fields must be an exact OwnedMapV1")
    return fields


def validate_owned_intent_invariants_v1(intent: OwnedIntentV1) -> None:
    """Check cross-field canonical form after every child has been admitted."""

    fields = _owned_field_map(intent)
    kind_text = intent_kind_text_v1(intent.kind)
    if (
        kind_text
        in (
            IntentKind.SWAP_EXACT_IN.value,
            IntentKind.SWAP_EXACT_OUT.value,
            IntentKind.ROUTE_EXACT_IN.value,
            IntentKind.ROUTE_EXACT_OUT.value,
        )
        and fields["asset_in"] == fields["asset_out"]
    ):
        raise ValueError("intent input and output assets must differ")
    if kind_text == IntentKind.CREATE_POOL.value:
        asset0 = fields["asset0"]
        asset1 = fields["asset1"]
        normalized_pair = normalize_pool_asset_pair(cast(str, asset0), cast(str, asset1))
        if normalized_pair != (asset0, asset1):
            raise ValueError("create-pool assets are not canonical")
        curve_tag = fields.get("curve_tag")
        curve_params = fields.get("curve_params")
        normalized_curve = normalize_curve_config(
            curve_tag=curve_tag,
            curve_params=curve_params,
        )
        if curve_tag is not None and normalized_curve[0] != curve_tag:
            raise ValueError("create-pool curve tag is not canonical")
        if curve_params is not None and normalized_curve[1] != curve_params:
            raise ValueError("create-pool curve params are not canonical")
    if kind_text in (
        IntentKind.ROUTE_EXACT_IN.value,
        IntentKind.ROUTE_EXACT_OUT.value,
    ):
        leg_indices = cast(tuple[int, ...], fields["leg_indices"])
        if any(
            leg_indices[index - 1] >= leg_indices[index] for index in range(1, len(leg_indices))
        ):
            raise ValueError("route leg indices are not strictly increasing")
