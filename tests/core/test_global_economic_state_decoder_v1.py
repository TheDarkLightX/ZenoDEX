"""Complete V1 decoding preserves exact data and refuses lossy normalization."""

from __future__ import annotations

import json
from copy import deepcopy
from dataclasses import fields
from enum import Enum
from typing import Any

import pytest

from src.core import global_settlement_types_v1 as types
from src.core.global_economic_state_decoder_v1 import (
    GLOBAL_ECONOMIC_STATE_FIELDS_V1,
    GLOBAL_ECONOMIC_STATE_TABLES_V1,
    GlobalEconomicStateDecodeLimitV1,
    decode_global_economic_state_v1,
)


class _Text(str):
    pass


class _Integer(int):
    pass


class _Mapping(dict):
    pass


class _Array(list):
    pass


class _ForeignStatus(str, Enum):
    OPEN = "OPEN"


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _complete_state() -> types.GlobalEconomicStateV1:
    """Every table and every terminal/outbox status has a retained value."""
    amounts = tuple(
        types.EconomicAmountV1(owner, "asset", "local", n)
        for owner, n in (("alice", 0), ("bob", 9))
    )
    return types.GlobalEconomicStateV1(
        chain_id="decoder-test-chain",
        deployment_root=_root(1),
        writer_epoch=0,
        height=types.MAX_U64_V1,
        profile_root=_root(2),
        lane_roots=tuple(
            types.LaneStateRootV1(lane, _root(100 + index), index == 0, _root(200 + index))
            for index, lane in enumerate(types.ALL_LANE_IDS_V1)
        ),
        balances=amounts,
        supplies=(
            types.AssetSupplyV1("asset", 0),
            types.AssetSupplyV1("second", types.MAX_ATOMS_V1),
        ),
        custody=amounts,
        liabilities=amounts,
        reserves=amounts,
        oracle_occurrences=(
            types.OracleOccurrenceStateV1("oracle-a", _root(3), 0, False),
            types.OracleOccurrenceStateV1("oracle-b", _root(4), types.MAX_U64_V1, True),
        ),
        replay_state=(
            types.ReplayStateV1("replay-a", _root(5)),
            types.ReplayStateV1("replay-b", _root(6)),
        ),
        terminal_obligations=tuple(
            types.TerminalObligationV1(
                f"terminal-{index}", types.LaneIdV1.ASSET_TRANSFER, "alice", "asset", index, status
            )
            for index, status in enumerate(types.TerminalObligationStatusV1)
        ),
        history_root=types.ZERO_ROOT_V1,
        outbox=tuple(
            types.OutboxStateV1(_root(300 + index), "destination", _root(7), _root(8), status)
            for index, status in enumerate(types.OutboxStatusV1)
        ),
    )


def _raw() -> dict[str, Any]:
    return json.loads(types.canonical_global_bytes_v1(_complete_state()))


def test_closed_table_registry_covers_the_complete_current_v1_state() -> None:
    assert GLOBAL_ECONOMIC_STATE_FIELDS_V1 == {
        "schema",
        *(field.name for field in fields(types.GlobalEconomicStateV1)),
    }
    assert tuple((name, limit) for name, _, limit in GLOBAL_ECONOMIC_STATE_TABLES_V1) == (
        ("lane_roots", 12),
        ("balances", 4096),
        ("supplies", 256),
        ("custody", 4096),
        ("liabilities", 4096),
        ("reserves", 4096),
        ("oracle_occurrences", 4096),
        ("replay_state", 4096),
        ("terminal_obligations", 4096),
        ("outbox", 4096),
    )
    assert tuple(status.value for status in types.TerminalObligationStatusV1) == (
        "OPEN",
        "DRAINED",
        "TOMBSTONED",
    )
    assert tuple(status.value for status in types.OutboxStatusV1) == ("PENDING", "ACKNOWLEDGED")


def test_complete_roundtrip_retains_all_rows_roots_and_owns_the_decoded_values() -> None:
    original, raw = _complete_state(), _raw()
    decoded = decode_global_economic_state_v1(raw)
    assert decoded == original
    assert decoded.state_root == original.state_root
    assert types.canonical_global_bytes_v1(decoded) == types.canonical_global_bytes_v1(original)
    for name, row_type, _ in GLOBAL_ECONOMIC_STATE_TABLES_V1:
        assert type(getattr(decoded, name)) is tuple
        assert all(type(row) is row_type for row in getattr(decoded, name))
        raw[name][0].clear()
        raw[name].clear()
    raw.clear()
    assert decoded == original


@pytest.mark.parametrize("missing", sorted(GLOBAL_ECONOMIC_STATE_FIELDS_V1))
def test_every_top_level_field_is_required(missing: str) -> None:
    raw = _raw()
    del raw[missing]
    with pytest.raises(ValueError, match="field set"):
        decode_global_economic_state_v1(raw)


@pytest.mark.parametrize("name,row_type,limit", GLOBAL_ECONOMIC_STATE_TABLES_V1)
def test_each_row_field_is_required_and_unknown_fields_are_refused(
    name: str, row_type: type, limit: int
) -> None:
    raw = _raw()
    for field in fields(row_type):
        changed = deepcopy(raw)
        del changed[name][0][field.name]
        with pytest.raises(ValueError, match="field set"):
            decode_global_economic_state_v1(changed)
    raw[name][0]["unknown"] = 0
    with pytest.raises(ValueError, match="field set"):
        decode_global_economic_state_v1(raw)


def test_unknown_top_fields_and_equivalent_nonexact_mapping_keys_are_refused() -> None:
    raw = _raw()
    for changed in (
        {**raw, "unknown": 0},
        {_Text(key) if key == "height" else key: value for key, value in raw.items()},
    ):
        with pytest.raises(ValueError, match="field set"):
            decode_global_economic_state_v1(changed)
    raw["balances"][0] = {_Text(key): value for key, value in raw["balances"][0].items()}
    with pytest.raises(ValueError, match="field set"):
        decode_global_economic_state_v1(raw)


@pytest.mark.parametrize("value", (None, (), [], 1, _Mapping()))
def test_nonexact_top_mappings_are_refused(value: object) -> None:
    with pytest.raises(ValueError, match="field set"):
        decode_global_economic_state_v1(value)


@pytest.mark.parametrize("name,row_type,limit", GLOBAL_ECONOMIC_STATE_TABLES_V1)
def test_each_table_requires_exact_arrays_and_rows(name: str, row_type: type, limit: int) -> None:
    raw = _raw()
    for rows in (tuple(raw[name]), _Array(raw[name]), None):
        with pytest.raises(TypeError, match="exact array"):
            decode_global_economic_state_v1({**raw, name: rows})
    for row in (_Mapping(raw[name][0]), None, []):
        with pytest.raises(ValueError, match="field set"):
            decode_global_economic_state_v1({**raw, name: [row, *raw[name][1:]]})


@pytest.mark.parametrize("name,row_type,limit", GLOBAL_ECONOMIC_STATE_TABLES_V1)
def test_each_table_ceiling_rejects_before_row_decoding(
    name: str, row_type: type, limit: int
) -> None:
    raw = _raw()
    with pytest.raises(GlobalEconomicStateDecodeLimitV1, match=name):
        decode_global_economic_state_v1({**raw, name: [{}] * (limit + 1)})


@pytest.mark.parametrize("name,row_type,limit", GLOBAL_ECONOMIC_STATE_TABLES_V1)
def test_every_table_rejects_reordering_and_duplicate_keys(
    name: str, row_type: type, limit: int
) -> None:
    raw = _raw()
    reordered = [raw[name][1], raw[name][0], *raw[name][2:]]
    duplicate = [raw[name][0], raw[name][0], *raw[name][2:]]
    for changed in (reordered, duplicate):
        with pytest.raises(ValueError, match="canonical|unique"):
            decode_global_economic_state_v1({**raw, name: changed})


@pytest.mark.parametrize(
    "name", ("balances", "custody", "liabilities", "reserves", "supplies", "terminal_obligations")
)
def test_equivalent_keys_with_distinct_amounts_cannot_hide_duplicate_claims(name: str) -> None:
    raw = _raw()
    raw[name][1] = {**raw[name][0], "amount_atoms": raw[name][0]["amount_atoms"] + 1}
    with pytest.raises(ValueError, match="unique"):
        decode_global_economic_state_v1(raw)


def test_distinct_replay_ids_cannot_reuse_one_occurrence() -> None:
    raw = _raw()
    raw["replay_state"][1]["occurrence_id"] = raw["replay_state"][0]["occurrence_id"]
    with pytest.raises(ValueError, match="replay occurrence ids must be unique"):
        decode_global_economic_state_v1(raw)


@pytest.mark.parametrize(
    "table,field,value",
    (
        (None, "schema", _Text(types.GLOBAL_SETTLEMENT_ABI_V1)),
        (None, "schema", "GlobalSettlementABI V2"),
        (None, "chain_id", _Text("chain")),
        (None, "deployment_root", _Text(_root(1))),
        (None, "writer_epoch", _Integer(0)),
        (None, "height", True),
        ("lane_roots", "enabled", 1),
        ("lane_roots", "lane_id", types.LaneIdV1.ASSET_TRANSFER),
        ("lane_roots", "lane_id", _Text("ASSET_TRANSFER")),
        ("lane_roots", "lane_id", "UNKNOWN_LANE"),
        ("balances", "amount_atoms", True),
        ("balances", "amount_atoms", _Integer(1)),
        ("balances", "amount_atoms", "1"),
        ("balances", "owner", _Text("alice")),
        ("oracle_occurrences", "finalized", 0),
        ("terminal_obligations", "status", _Text("OPEN")),
        ("terminal_obligations", "status", _ForeignStatus.OPEN),
        ("terminal_obligations", "status", types.TerminalObligationStatusV1.OPEN),
        ("terminal_obligations", "status", "ACKNOWLEDGED"),
        ("outbox", "status", types.OutboxStatusV1.PENDING),
        ("outbox", "status", "OPEN"),
    ),
)
def test_nonexact_scalars_and_foreign_enum_variants_are_refused(
    table: str | None, field: str, value: object
) -> None:
    raw = _raw()
    target = raw if table is None else raw[table][0]
    target[field] = value
    with pytest.raises((TypeError, ValueError)):
        decode_global_economic_state_v1(raw)


@pytest.mark.parametrize(
    "table,field,maximum",
    (
        (None, "height", types.MAX_U64_V1),
        (None, "writer_epoch", types.MAX_U64_V1),
        ("oracle_occurrences", "observed_height", types.MAX_U64_V1),
        ("balances", "amount_atoms", types.MAX_ATOMS_V1),
        ("custody", "amount_atoms", types.MAX_ATOMS_V1),
        ("liabilities", "amount_atoms", types.MAX_ATOMS_V1),
        ("reserves", "amount_atoms", types.MAX_ATOMS_V1),
        ("supplies", "amount_atoms", types.MAX_ATOMS_V1),
        ("terminal_obligations", "amount_atoms", types.MAX_ATOMS_V1),
    ),
)
def test_integer_boundaries_are_exact_and_overflow_refuses(
    table: str | None, field: str, maximum: int
) -> None:
    for value in (0, 1, maximum - 1, maximum, -1, maximum + 1):
        raw = _raw()
        target = raw if table is None else raw[table][0]
        target[field] = value
        if value < 0 or value > maximum:
            with pytest.raises(ValueError):
                decode_global_economic_state_v1(raw)
        else:
            decoded = decode_global_economic_state_v1(raw)
            owned = decoded if table is None else getattr(decoded, table)[0]
            assert getattr(owned, field) == value


def test_all_lanes_are_required_even_when_economic_tables_are_empty() -> None:
    raw = _raw()
    for name, _, _ in GLOBAL_ECONOMIC_STATE_TABLES_V1:
        if name != "lane_roots":
            raw[name] = []
    assert decode_global_economic_state_v1(raw).balances == ()
    raw["lane_roots"].pop()
    with pytest.raises(ValueError, match="every ABI V1 lane"):
        decode_global_economic_state_v1(raw)


def test_core_preserves_complete_tables_above_the_separate_observer_aggregate_budget() -> None:
    raw = _raw()
    for name in ("balances", "liabilities"):
        raw[name] = [
            {
                "owner": f"owner-{index:04d}",
                "asset": "asset",
                "custody_domain": "local",
                "amount_atoms": index,
            }
            for index in range(types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1)
        ]
    decoded = decode_global_economic_state_v1(raw)
    assert len(decoded.balances) == len(decoded.liabilities) == 4096
    assert decoded.balances[-1].owner == decoded.liabilities[-1].owner == "owner-4095"
    assert sum(len(getattr(decoded, name)) for name, _, _ in GLOBAL_ECONOMIC_STATE_TABLES_V1) > 8192
    assert json.loads(types.canonical_global_bytes_v1(decoded)) == raw


@pytest.mark.parametrize("budget_delta", (-1, 0, 1))
def test_observer_aggregate_budget_and_limit_class_remain_separate(budget_delta: int) -> None:
    # This adapter comparison protects the extraction's resource-limit contract.
    from src.integration import global_allocation_shadow_v1 as shadow

    raw = _raw()
    raw["balances"] = [
        {
            "owner": f"owner-{index:04d}",
            "asset": "asset",
            "custody_domain": "local",
            "amount_atoms": index,
        }
        for index in range(types.MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1)
    ]
    other_rows = sum(
        len(raw[name]) for name, _, _ in GLOBAL_ECONOMIC_STATE_TABLES_V1 if name != "liabilities"
    )
    raw["liabilities"] = raw["balances"][
        : shadow.MAX_SHADOW_STATE_ROWS_V1 + budget_delta - other_rows
    ]
    decoded = decode_global_economic_state_v1(raw)
    assert (
        sum(len(getattr(decoded, name)) for name, _, _ in GLOBAL_ECONOMIC_STATE_TABLES_V1)
        == 8192 + budget_delta
    )
    if budget_delta > 0:
        with pytest.raises(shadow._ObservationLimitV1, match="row budget"):
            shadow.decode_shadow_state_v1(raw)
    else:
        assert shadow.decode_shadow_state_v1(raw) == decoded
