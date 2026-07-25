"""Closed bounded schema for composition-owned settlement authority values."""

from __future__ import annotations

from ..state.owned_collections import OwnedEnumV1
from ..state.owned_json import (
    JSON_OBJECT_SCHEMA_V1,
    MAX_OWNED_JSON_CONTAINER_ITEMS_V1,
)
from ..state.snapshot_combinators import (
    DeclaredFieldV1,
    EnumRegistrationV1,
    ExactEnum,
    ExactInt,
    ExactPair,
    ExactString,
    OptionalValue,
    RecordOf,
    RecordRegistrationV1,
    SchemaRegistrationV1,
    SchemaV1,
    SequenceOf,
    SequenceSourceKind,
    StringRuleV1,
)
from ..state.state_snapshot_schema import (
    StateEnumTagV1,
    StateRecordTagV1,
    state_enum_tag_ordinal_v1,
)
from ..state.state_snapshot_values import FCIS_STATE_SCHEMA_REVISION_V1
from .domain_limits import DEX_POOL_RESERVE_MAX
from .settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement
from .settlement_snapshots import (
    OwnedBalanceDeltaV1,
    OwnedFillV1,
    OwnedLPDeltaV1,
    OwnedReserveDeltaV1,
    OwnedSettlementV1,
)

SETTLEMENT_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/authority/settlement/v1"
MAX_SETTLEMENT_INTENTS_V1 = 256
MAX_SETTLEMENT_GRAPH_ITEMS_V1 = MAX_OWNED_JSON_CONTAINER_ITEMS_V1
MAX_SETTLEMENT_AMOUNT_V1 = DEX_POOL_RESERVE_MAX
# One canonical delta entry may aggregate the maximum contribution from every
# bounded intent in the batch. Route totals retain the same per-intent cap.
MAX_SETTLEMENT_DELTA_COMPONENT_V1 = MAX_SETTLEMENT_INTENTS_V1 * DEX_POOL_RESERVE_MAX


def _field(name: str, schema: SchemaV1) -> DeclaredFieldV1:
    return DeclaredFieldV1(name, schema)


INTENT_ID_V1 = ExactString(
    StringRuleV1.LOWERCASE_0X_HEX,
    66,
    exact_utf8_bytes=66,
    max_characters=66,
)
TEXT_256_V1 = ExactString(StringRuleV1.NON_EMPTY, 1_024, max_characters=256)
TEXT_512_V1 = ExactString(StringRuleV1.NON_EMPTY, 2_048, max_characters=512)
EXACT_TEXT_4096_V1 = ExactString(
    StringRuleV1.EXACT_TEXT,
    16_384,
    max_characters=4_096,
)
OPTIONAL_AMOUNT_V1 = OptionalValue(ExactInt(0, MAX_SETTLEMENT_AMOUNT_V1))
DELTA_COMPONENT_V1 = ExactInt(0, MAX_SETTLEMENT_DELTA_COMPONENT_V1)

FILL_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FILL,
    (
        _field("intent_id", INTENT_ID_V1),
        _field("action", ExactEnum(StateEnumTagV1.FILL_ACTION)),
        _field("reason", OptionalValue(EXACT_TEXT_4096_V1)),
        _field("amount_in_filled", OPTIONAL_AMOUNT_V1),
        _field("amount_out_filled", OPTIONAL_AMOUNT_V1),
        _field("fee_paid", OPTIONAL_AMOUNT_V1),
        _field("protocol_fee_paid", OPTIONAL_AMOUNT_V1),
        _field("amount0_used", OPTIONAL_AMOUNT_V1),
        _field("amount1_used", OPTIONAL_AMOUNT_V1),
        _field("lp_minted", OPTIONAL_AMOUNT_V1),
        _field("amount0_out", OPTIONAL_AMOUNT_V1),
        _field("amount1_out", OPTIONAL_AMOUNT_V1),
        _field("lp_burned", OPTIONAL_AMOUNT_V1),
        _field("reserve_in_before", OPTIONAL_AMOUNT_V1),
        _field("reserve_out_before", OPTIONAL_AMOUNT_V1),
    ),
)

BALANCE_DELTA_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.BALANCE_DELTA,
    (
        _field("pubkey", TEXT_512_V1),
        _field("asset", TEXT_256_V1),
        _field("delta_add", DELTA_COMPONENT_V1),
        _field("delta_sub", DELTA_COMPONENT_V1),
    ),
)
RESERVE_DELTA_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.RESERVE_DELTA,
    (
        _field("pool_id", TEXT_256_V1),
        _field("asset", TEXT_256_V1),
        _field("delta_add", DELTA_COMPONENT_V1),
        _field("delta_sub", DELTA_COMPONENT_V1),
    ),
)
LP_DELTA_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.LP_DELTA,
    (
        _field("pubkey", TEXT_512_V1),
        _field("pool_id", TEXT_256_V1),
        _field("delta_add", DELTA_COMPONENT_V1),
        _field("delta_sub", DELTA_COMPONENT_V1),
    ),
)

SETTLEMENT_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.SETTLEMENT,
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
        _field("batch_ref", EXACT_TEXT_4096_V1),
        _field(
            "included_intents",
            SequenceOf(
                (SequenceSourceKind.EXACT_LIST, SequenceSourceKind.EXACT_TUPLE),
                ExactPair(INTENT_ID_V1, ExactEnum(StateEnumTagV1.FILL_ACTION)),
                0,
                MAX_SETTLEMENT_INTENTS_V1,
            ),
        ),
        _field(
            "fills",
            SequenceOf(
                (SequenceSourceKind.EXACT_LIST, SequenceSourceKind.EXACT_TUPLE),
                FILL_SCHEMA_V1,
                0,
                MAX_SETTLEMENT_INTENTS_V1,
            ),
        ),
        _field(
            "balance_deltas",
            SequenceOf(
                (SequenceSourceKind.EXACT_LIST, SequenceSourceKind.EXACT_TUPLE),
                BALANCE_DELTA_SCHEMA_V1,
                0,
                MAX_SETTLEMENT_GRAPH_ITEMS_V1,
            ),
        ),
        _field(
            "reserve_deltas",
            SequenceOf(
                (SequenceSourceKind.EXACT_LIST, SequenceSourceKind.EXACT_TUPLE),
                RESERVE_DELTA_SCHEMA_V1,
                0,
                MAX_SETTLEMENT_GRAPH_ITEMS_V1,
            ),
        ),
        _field(
            "lp_deltas",
            SequenceOf(
                (SequenceSourceKind.EXACT_LIST, SequenceSourceKind.EXACT_TUPLE),
                LP_DELTA_SCHEMA_V1,
                0,
                MAX_SETTLEMENT_GRAPH_ITEMS_V1,
            ),
        ),
        _field(
            "events",
            OptionalValue(
                SequenceOf(
                    (SequenceSourceKind.EXACT_LIST, SequenceSourceKind.EXACT_TUPLE),
                    JSON_OBJECT_SCHEMA_V1,
                    1,
                    MAX_SETTLEMENT_GRAPH_ITEMS_V1,
                )
            ),
        ),
    ),
)

SETTLEMENT_ENUM_REGISTRATIONS_V1 = (EnumRegistrationV1(StateEnumTagV1.FILL_ACTION, FillAction),)
SETTLEMENT_RECORD_REGISTRATIONS_V1 = (
    RecordRegistrationV1(StateRecordTagV1.FILL, Fill, OwnedFillV1),
    RecordRegistrationV1(
        StateRecordTagV1.BALANCE_DELTA,
        BalanceDelta,
        OwnedBalanceDeltaV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.RESERVE_DELTA,
        ReserveDelta,
        OwnedReserveDeltaV1,
    ),
    RecordRegistrationV1(StateRecordTagV1.LP_DELTA, LPDelta, OwnedLPDeltaV1),
    RecordRegistrationV1(
        StateRecordTagV1.SETTLEMENT,
        Settlement,
        OwnedSettlementV1,
    ),
)
SETTLEMENT_SCHEMA_REGISTRATIONS_V1 = (
    SchemaRegistrationV1(SETTLEMENT_ADMISSION_SCHEMA_ID_V1, SETTLEMENT_SCHEMA_V1),
)


def fill_action_text_v1(action: OwnedEnumV1) -> str:
    if (
        type(action) is not OwnedEnumV1
        or action.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or action.enum_tag_ordinal != state_enum_tag_ordinal_v1(StateEnumTagV1.FILL_ACTION)
        or not 0 <= action.member_ordinal < len(tuple(FillAction))
    ):
        raise TypeError("owned fill action metadata mismatch")
    return tuple(FillAction)[action.member_ordinal].value
