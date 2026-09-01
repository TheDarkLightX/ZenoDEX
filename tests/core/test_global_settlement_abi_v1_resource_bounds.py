from __future__ import annotations

import re
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest

from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1,
    MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1,
    MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1,
    MAX_EFFECT_PLAN_LANE_WRITES_V1,
    MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1,
    MAX_EFFECT_PLAN_ROWS_V1,
    MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
    MAX_GLOBAL_ORACLE_ROWS_V1,
    MAX_GLOBAL_OUTBOX_ROWS_V1,
    MAX_GLOBAL_REPLAY_ROWS_V1,
    MAX_GLOBAL_SUPPLY_ROWS_V1,
    MAX_GLOBAL_TERMINAL_ROWS_V1,
    ZERO_ROOT_V1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneStateRootV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _state() -> GlobalEconomicStateV1:
    return GlobalEconomicStateV1(
        chain_id="resource-bound-test",
        deployment_root=_root(1),
        writer_epoch=1,
        height=1,
        profile_root=_root(2),
        lane_roots=tuple(
            LaneStateRootV1(lane_id, _root(100 + index), False, ZERO_ROOT_V1)
            for index, lane_id in enumerate(ALL_LANE_IDS_V1)
        ),
    )


def _replace_state_field(
    state: GlobalEconomicStateV1,
    field_name: str,
    value: tuple[object, ...],
) -> GlobalEconomicStateV1:
    return replace(state, **cast(Any, {field_name: value}))


_EFFECT_PLAN_LIMITS = (
    ("rows", MAX_EFFECT_PLAN_ROWS_V1, "effect plan rows"),
    (
        "asset_conservation",
        MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1,
        "effect plan asset conservation",
    ),
    (
        "fee_conservation",
        MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1,
        "effect plan fee conservation",
    ),
    ("lane_writes", MAX_EFFECT_PLAN_LANE_WRITES_V1, "effect plan lane writes"),
    (
        "occurrence_consumptions",
        MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1,
        "effect plan occurrence consumptions",
    ),
    (
        "external_outbox_enqueue",
        MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1,
        "effect plan external outbox",
    ),
)


@pytest.mark.parametrize(("field_name", "limit", "error_name"), _EFFECT_PLAN_LIMITS)
def test_effect_plan_bounds_accept_limit_and_reject_next_before_traversal(
    field_name: str,
    limit: int,
    error_name: str,
) -> None:
    values: dict[str, Any] = {name: () for name, _, _ in _EFFECT_PLAN_LIMITS}
    values[field_name] = (object(),) * limit

    with pytest.raises(TypeError):
        GlobalEconomicEffectPlanV1(**values)

    values[field_name] = (object(),) * (limit + 1)
    with pytest.raises(
        ValueError,
        match=rf"{re.escape(error_name)} exceeds its {limit}-item ceiling",
    ):
        GlobalEconomicEffectPlanV1(**values)


_GLOBAL_STATE_LIMITS = (
    ("balances", MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1, "global state balances"),
    ("supplies", MAX_GLOBAL_SUPPLY_ROWS_V1, "global state supplies"),
    ("custody", MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1, "global state custody"),
    (
        "liabilities",
        MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
        "global state liabilities",
    ),
    ("reserves", MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1, "global state reserves"),
    (
        "oracle_occurrences",
        MAX_GLOBAL_ORACLE_ROWS_V1,
        "global state oracle occurrences",
    ),
    ("replay_state", MAX_GLOBAL_REPLAY_ROWS_V1, "global state replay state"),
    (
        "terminal_obligations",
        MAX_GLOBAL_TERMINAL_ROWS_V1,
        "global state terminal obligations",
    ),
    ("outbox", MAX_GLOBAL_OUTBOX_ROWS_V1, "global state outbox"),
)


@pytest.mark.parametrize(("field_name", "limit", "error_name"), _GLOBAL_STATE_LIMITS)
def test_global_state_bounds_accept_limit_and_reject_next_before_traversal(
    field_name: str,
    limit: int,
    error_name: str,
) -> None:
    baseline = _state()

    with pytest.raises(TypeError):
        _replace_state_field(baseline, field_name, (object(),) * limit)

    with pytest.raises(
        ValueError,
        match=rf"{re.escape(error_name)} exceeds its {limit}-item ceiling",
    ):
        _replace_state_field(baseline, field_name, (object(),) * (limit + 1))


def test_python_and_rust_v1_collection_limits_are_frozen_and_equal() -> None:
    expected = {
        "MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1": 256,
        "MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1": 4_096,
        "MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1": 256,
        "MAX_EFFECT_PLAN_LANE_WRITES_V1": 12,
        "MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1": 4_096,
        "MAX_EFFECT_PLAN_ROWS_V1": 4_096,
        "MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1": 4_096,
        "MAX_GLOBAL_ORACLE_ROWS_V1": 4_096,
        "MAX_GLOBAL_OUTBOX_ROWS_V1": 4_096,
        "MAX_GLOBAL_REPLAY_ROWS_V1": 4_096,
        "MAX_GLOBAL_SUPPLY_ROWS_V1": 256,
        "MAX_GLOBAL_TERMINAL_ROWS_V1": 4_096,
    }
    python_limits = {
        "MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1": (MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1),
        "MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1": (MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1),
        "MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1": (MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1),
        "MAX_EFFECT_PLAN_LANE_WRITES_V1": MAX_EFFECT_PLAN_LANE_WRITES_V1,
        "MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1": (MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1),
        "MAX_EFFECT_PLAN_ROWS_V1": MAX_EFFECT_PLAN_ROWS_V1,
        "MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1": MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
        "MAX_GLOBAL_ORACLE_ROWS_V1": MAX_GLOBAL_ORACLE_ROWS_V1,
        "MAX_GLOBAL_OUTBOX_ROWS_V1": MAX_GLOBAL_OUTBOX_ROWS_V1,
        "MAX_GLOBAL_REPLAY_ROWS_V1": MAX_GLOBAL_REPLAY_ROWS_V1,
        "MAX_GLOBAL_SUPPLY_ROWS_V1": MAX_GLOBAL_SUPPLY_ROWS_V1,
        "MAX_GLOBAL_TERMINAL_ROWS_V1": MAX_GLOBAL_TERMINAL_ROWS_V1,
    }
    assert python_limits == expected

    rust_source = (
        Path(__file__).resolve().parents[2] / "zk/global_settlement_abi_v1/src/canonical.rs"
    ).read_text(encoding="utf-8")
    rust_limits = {
        name: int(value.replace("_", ""))
        for name, value in re.findall(
            r"pub const (MAX_(?:EFFECT_PLAN|GLOBAL_)[A-Z0-9_]+): usize = ([0-9_]+);",
            rust_source,
        )
    }
    assert {name: rust_limits[name] for name in expected} == expected
