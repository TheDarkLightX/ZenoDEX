"""Exact composition-owned settlement values for the FCIS authority graph."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, cast, final

from ..state.canonical import canonical_json_bytes
from ..state.owned_collections import OwnedEnumV1
from ..state.owned_json import (
    JsonProjectionV1,
    OwnedJsonObjectV1,
    _admit_graph_value,
    _project_owned_json_unchecked,
)
from ..state.state_snapshot_schema import StateRecordTagV1
from .settlement import Settlement


@final
@dataclass(frozen=True, slots=True)
class OwnedFillV1:
    intent_id: str
    action: OwnedEnumV1
    reason: str | None
    amount_in_filled: int | None
    amount_out_filled: int | None
    fee_paid: int | None
    protocol_fee_paid: int | None
    amount0_used: int | None
    amount1_used: int | None
    lp_minted: int | None
    amount0_out: int | None
    amount1_out: int | None
    lp_burned: int | None
    reserve_in_before: int | None
    reserve_out_before: int | None


@final
@dataclass(frozen=True, slots=True)
class OwnedBalanceDeltaV1:
    pubkey: str
    asset: str
    delta_add: int
    delta_sub: int


@final
@dataclass(frozen=True, slots=True)
class OwnedReserveDeltaV1:
    pool_id: str
    asset: str
    delta_add: int
    delta_sub: int


@final
@dataclass(frozen=True, slots=True)
class OwnedLPDeltaV1:
    pubkey: str
    pool_id: str
    delta_add: int
    delta_sub: int


OwnedIncludedIntentV1: TypeAlias = tuple[str, OwnedEnumV1]


@final
@dataclass(frozen=True, slots=True)
class OwnedSettlementV1:
    module: str
    version: str
    batch_ref: str
    included_intents: tuple[OwnedIncludedIntentV1, ...]
    fills: tuple[OwnedFillV1, ...]
    balance_deltas: tuple[OwnedBalanceDeltaV1, ...]
    reserve_deltas: tuple[OwnedReserveDeltaV1, ...]
    lp_deltas: tuple[OwnedLPDeltaV1, ...]
    events: tuple[OwnedJsonObjectV1, ...] | None


SettlementSourceV1: TypeAlias = Settlement | OwnedSettlementV1


def _record_field(
    values: tuple[tuple[str, object], ...],
    index: int,
    expected_name: str,
) -> object:
    if type(values) is not tuple or index >= len(values):
        raise ValueError("settlement record field registry drift")
    field = values[index]
    if type(field) is not tuple or len(field) != 2 or field[0] != expected_name:
        raise ValueError("settlement record field registry drift")
    return field[1]


def _construct_fill(values: tuple[tuple[str, object], ...]) -> OwnedFillV1:
    names = (
        "intent_id",
        "action",
        "reason",
        "amount_in_filled",
        "amount_out_filled",
        "fee_paid",
        "protocol_fee_paid",
        "amount0_used",
        "amount1_used",
        "lp_minted",
        "amount0_out",
        "amount1_out",
        "lp_burned",
        "reserve_in_before",
        "reserve_out_before",
    )
    fields = tuple(_record_field(values, index, name) for index, name in enumerate(names))
    return OwnedFillV1(
        cast(str, fields[0]),
        cast(OwnedEnumV1, fields[1]),
        cast(str | None, fields[2]),
        cast(int | None, fields[3]),
        cast(int | None, fields[4]),
        cast(int | None, fields[5]),
        cast(int | None, fields[6]),
        cast(int | None, fields[7]),
        cast(int | None, fields[8]),
        cast(int | None, fields[9]),
        cast(int | None, fields[10]),
        cast(int | None, fields[11]),
        cast(int | None, fields[12]),
        cast(int | None, fields[13]),
        cast(int | None, fields[14]),
    )


def _construct_balance_delta(
    values: tuple[tuple[str, object], ...],
) -> OwnedBalanceDeltaV1:
    return OwnedBalanceDeltaV1(
        cast(str, _record_field(values, 0, "pubkey")),
        cast(str, _record_field(values, 1, "asset")),
        cast(int, _record_field(values, 2, "delta_add")),
        cast(int, _record_field(values, 3, "delta_sub")),
    )


def _construct_reserve_delta(
    values: tuple[tuple[str, object], ...],
) -> OwnedReserveDeltaV1:
    return OwnedReserveDeltaV1(
        cast(str, _record_field(values, 0, "pool_id")),
        cast(str, _record_field(values, 1, "asset")),
        cast(int, _record_field(values, 2, "delta_add")),
        cast(int, _record_field(values, 3, "delta_sub")),
    )


def _construct_lp_delta(values: tuple[tuple[str, object], ...]) -> OwnedLPDeltaV1:
    return OwnedLPDeltaV1(
        cast(str, _record_field(values, 0, "pubkey")),
        cast(str, _record_field(values, 1, "pool_id")),
        cast(int, _record_field(values, 2, "delta_add")),
        cast(int, _record_field(values, 3, "delta_sub")),
    )


def _has_duplicate_intent_id(items: tuple[tuple[str, object], ...]) -> bool:
    return any(
        items[left][0] == items[right][0]
        for left in range(len(items))
        for right in range(left + 1, len(items))
    )


def _validate_settlement_invariants(value: OwnedSettlementV1) -> None:
    included = cast(tuple[tuple[str, object], ...], value.included_intents)
    fill_ids = tuple((fill.intent_id, fill.action) for fill in value.fills)
    if _has_duplicate_intent_id(included):
        raise ValueError("included_intents contains duplicate intent IDs")
    if _has_duplicate_intent_id(fill_ids):
        raise ValueError("fills contains duplicate intent IDs")
    if any(
        all(fill.intent_id != intent_id for intent_id, _action in value.included_intents)
        for fill in value.fills
    ):
        raise ValueError("fill intent ID is absent from included_intents")

    from .settlement_schema import fill_action_text_v1

    included_fills = tuple(
        intent_id
        for intent_id, action in value.included_intents
        if fill_action_text_v1(action) == "FILL"
    )
    detailed_fills = tuple(
        fill.intent_id for fill in value.fills if fill_action_text_v1(fill.action) == "FILL"
    )
    if len(included_fills) != len(detailed_fills) or any(
        intent_id not in detailed_fills for intent_id in included_fills
    ):
        raise ValueError("filled intent IDs and FILL details disagree")


def _construct_settlement(values: tuple[tuple[str, object], ...]) -> OwnedSettlementV1:
    owned = OwnedSettlementV1(
        cast(str, _record_field(values, 0, "module")),
        cast(str, _record_field(values, 1, "version")),
        cast(str, _record_field(values, 2, "batch_ref")),
        cast(tuple[OwnedIncludedIntentV1, ...], _record_field(values, 3, "included_intents")),
        cast(tuple[OwnedFillV1, ...], _record_field(values, 4, "fills")),
        cast(tuple[OwnedBalanceDeltaV1, ...], _record_field(values, 5, "balance_deltas")),
        cast(tuple[OwnedReserveDeltaV1, ...], _record_field(values, 6, "reserve_deltas")),
        cast(tuple[OwnedLPDeltaV1, ...], _record_field(values, 7, "lp_deltas")),
        cast(tuple[OwnedJsonObjectV1, ...] | None, _record_field(values, 8, "events")),
    )
    _validate_settlement_invariants(owned)
    return owned


def _construct_settlement_record(
    record_tag: Enum,
    values: tuple[tuple[str, object], ...],
) -> object:
    if record_tag is StateRecordTagV1.FILL and len(values) == 15:
        return _construct_fill(values)
    if record_tag is StateRecordTagV1.BALANCE_DELTA and len(values) == 4:
        return _construct_balance_delta(values)
    if record_tag is StateRecordTagV1.RESERVE_DELTA and len(values) == 4:
        return _construct_reserve_delta(values)
    if record_tag is StateRecordTagV1.LP_DELTA and len(values) == 4:
        return _construct_lp_delta(values)
    if record_tag is StateRecordTagV1.SETTLEMENT and len(values) == 9:
        return _construct_settlement(values)
    raise ValueError("unsupported settlement record tag or field registry drift")


def _project_owned_fill(value: OwnedFillV1) -> dict[str, JsonProjectionV1]:
    return {
        "intent_id": value.intent_id,
        "action": _fill_action_text(value.action),
        "reason": value.reason,
        "amount_in_filled": value.amount_in_filled,
        "amount_out_filled": value.amount_out_filled,
        "fee_paid": value.fee_paid,
        "protocol_fee_paid": value.protocol_fee_paid,
        "amount0_used": value.amount0_used,
        "amount1_used": value.amount1_used,
        "lp_minted": value.lp_minted,
        "amount0_out": value.amount0_out,
        "amount1_out": value.amount1_out,
        "lp_burned": value.lp_burned,
        "reserve_in_before": value.reserve_in_before,
        "reserve_out_before": value.reserve_out_before,
    }


def _fill_action_text(value: OwnedEnumV1) -> str:
    from .settlement_schema import fill_action_text_v1

    return fill_action_text_v1(value)


def _project_owned_settlement(
    value: OwnedSettlementV1,
) -> dict[str, JsonProjectionV1]:
    projection: dict[str, JsonProjectionV1] = {
        "module": value.module,
        "version": value.version,
        "batch_ref": value.batch_ref,
        "included_intents": [
            [intent_id, _fill_action_text(action)] for intent_id, action in value.included_intents
        ],
        "fills": [_project_owned_fill(fill) for fill in value.fills],
        "balance_deltas": [
            {
                "pubkey": delta.pubkey,
                "asset": delta.asset,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            }
            for delta in value.balance_deltas
        ],
        "reserve_deltas": [
            {
                "pool_id": delta.pool_id,
                "asset": delta.asset,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            }
            for delta in value.reserve_deltas
        ],
        "lp_deltas": [
            {
                "pubkey": delta.pubkey,
                "pool_id": delta.pool_id,
                "delta_add": delta.delta_add,
                "delta_sub": delta.delta_sub,
            }
            for delta in value.lp_deltas
        ],
    }
    if value.events:
        projection["events"] = [_project_owned_json_unchecked(event) for event in value.events]
    return projection


def snapshot_settlement(source: SettlementSourceV1) -> OwnedSettlementV1:
    """Admit one exact mutable/owned settlement through the sole profile."""

    from .settlement_schema import SETTLEMENT_ADMISSION_SCHEMA_ID_V1

    admitted = _admit_graph_value(SETTLEMENT_ADMISSION_SCHEMA_ID_V1, source)
    if type(admitted) is not OwnedSettlementV1:
        raise RuntimeError("closed settlement admission returned an impossible result")
    return admitted


def canonical_owned_settlement_bytes_v1(value: OwnedSettlementV1) -> bytes:
    """Encode the mounted operation-3 projection after full revalidation."""

    owned = snapshot_settlement(value)
    return canonical_json_bytes(_project_owned_settlement(owned))
