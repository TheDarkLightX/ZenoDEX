"""Exact complete GlobalSettlementABI V1 state decoding, without IO or authority.

The input is an already decoded JSON value. Byte-level canonicality and duplicate
JSON object keys must be checked by the byte decoder before calling this function.
Every state table is reconstructed in full under its existing V1 row ceiling.
"""

from __future__ import annotations

from dataclasses import fields
from typing import Any, Final

from . import global_settlement_types_v1 as types
from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1

GLOBAL_ECONOMIC_STATE_TABLES_V1: Final = (
    ("lane_roots", types.LaneStateRootV1, len(types.ALL_LANE_IDS_V1)),
    ("balances", types.EconomicAmountV1, types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1),
    ("supplies", types.AssetSupplyV1, types.MAX_GLOBAL_SUPPLY_ROWS_V1),
    ("custody", types.EconomicAmountV1, types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1),
    ("liabilities", types.EconomicAmountV1, types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1),
    ("reserves", types.EconomicAmountV1, types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1),
    ("oracle_occurrences", types.OracleOccurrenceStateV1, types.MAX_GLOBAL_ORACLE_ROWS_V1),
    ("replay_state", types.ReplayStateV1, types.MAX_GLOBAL_REPLAY_ROWS_V1),
    ("terminal_obligations", types.TerminalObligationV1, types.MAX_GLOBAL_TERMINAL_ROWS_V1),
    ("outbox", types.OutboxStateV1, types.MAX_GLOBAL_OUTBOX_ROWS_V1),
)
GLOBAL_ECONOMIC_STATE_FIELDS_V1: Final = frozenset(
    {
        "schema",
        "chain_id",
        "deployment_root",
        "writer_epoch",
        "height",
        "profile_root",
        "history_root",
        *(name for name, _row_type, _limit in GLOBAL_ECONOMIC_STATE_TABLES_V1),
    }
)


class GlobalEconomicStateDecodeLimitV1(ValueError):
    """A complete table exceeds its V1 bound; no partial state is returned."""


def _exact_mapping_v1(raw: object, expected: frozenset[str], label: str) -> dict[str, Any]:
    if type(raw) is not dict or any(type(key) is not str for key in raw) or set(raw) != expected:
        raise ValueError(f"global state {label} has an open field set")
    return dict(raw)


def _decode_row_v1(row_type: type[Any], raw: object) -> Any:
    owned = _exact_mapping_v1(raw, frozenset(field.name for field in fields(row_type)), "row")
    if "lane_id" in owned:
        if type(owned["lane_id"]) is not str:
            raise TypeError("global state lane id must be exact text")
        owned["lane_id"] = types.LaneIdV1(owned["lane_id"])
    status_type = {
        types.TerminalObligationV1: types.TerminalObligationStatusV1,
        types.OutboxStateV1: types.OutboxStatusV1,
    }.get(row_type)
    if status_type is not None:
        if type(owned["status"]) is not str:
            raise TypeError("global state status must be exact text")
        owned["status"] = status_type(owned["status"])
    return row_type(**owned)


def decode_global_economic_state_v1(raw: object) -> types.GlobalEconomicStateV1:
    """Own exact V1 data, validating closed fields, rows, scalars and order.

    The returned value carries no proof of store authenticity, complete history,
    receipt validity, ownership policy or current publication authority.
    """
    owned = _exact_mapping_v1(raw, GLOBAL_ECONOMIC_STATE_FIELDS_V1, "value")
    if type(owned["schema"]) is not str or owned["schema"] != types.GLOBAL_SETTLEMENT_ABI_V1:
        raise ValueError("global state schema mismatch")
    for name, _row_type, limit in GLOBAL_ECONOMIC_STATE_TABLES_V1:
        rows = owned[name]
        if type(rows) is not list:
            raise TypeError("global state table must be an exact array")
        if len(rows) > limit:
            raise GlobalEconomicStateDecodeLimitV1(
                f"global state {name} exceeds its {limit}-row ceiling"
            )
    del owned["schema"]
    for name, row_type, _limit in GLOBAL_ECONOMIC_STATE_TABLES_V1:
        owned[name] = tuple(_decode_row_v1(row_type, row) for row in owned[name])
    return _snapshot_state_v1(types.GlobalEconomicStateV1(**owned))
