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
    rust_matches = re.findall(
        r"pub const (MAX_(?:EFFECT_PLAN|GLOBAL_)[A-Z0-9_]+): usize = ([0-9_]+);",
        rust_source,
    )
    rust_limits = {name: int(value.replace("_", "")) for name, value in rust_matches}
    # Opus P24 NEW-12: a duplicate declaration (e.g. a trailing comment repeating
    # a bound) must not let last-occurrence-wins mask a value drift.
    assert len(rust_matches) == len(rust_limits)
    assert {name: rust_limits[name] for name in expected} == expected


def test_every_canonical_rust_bound_has_a_python_twin() -> None:
    """Opus P21 NEW-4: total parity over the whole crate, not a hand-maintained list.

    Every `pub const MAX_...` declaration in every .rs file under the crate's
    src/ tree (recursive), whatever its type
    spelling (primitive, CamelCase alias, or path-qualified) or spacing, must
    resolve through this single
    mapping with an equal value; a newly added Rust bound with no Python twin
    fails the key-set equality below instead of silently matching no regex."""

    from src.core import global_settlement_types_v1 as types

    crate_src = Path(__file__).resolve().parents[2] / "zk/global_settlement_abi_v1/src"
    rust_source = "\n".join(
        rust_file.read_text(encoding="utf-8") for rust_file in sorted(crate_src.rglob("*.rs"))
    )

    def evaluate(expression: str) -> int:
        expression = expression.strip()
        if expression == "u128::MAX":
            return (1 << 128) - 1
        if "<<" in expression:
            left, right = expression.split("<<")
            return int(left.strip().replace("_", "")) << int(right.strip().replace("_", ""))
        if "*" in expression:
            product = 1
            for factor in expression.split("*"):
                product *= int(factor.strip().replace("_", ""))
            return product
        return int(expression.replace("_", ""))

    rust_matches = re.findall(
        r"pub\s+const\s+(MAX_[A-Z0-9_]+)\s*:\s*[A-Za-z0-9_:]+\s*=\s*([^;]+);",
        rust_source,
        re.S,
    )
    rust_bounds = {name: evaluate(expression) for name, expression in rust_matches}
    # Opus P24 NEW-12: duplicate names (comment-masking) must fail, not last-win.
    assert len(rust_matches) == len(rust_bounds)
    import importlib

    twin_modules = [
        types,
        importlib.import_module("src.core.lane_module_receipt_verification_v1"),
        importlib.import_module("src.core.asset_transfer_policy_registry_v1"),
        importlib.import_module("src.core.economic_command_authorization_registry_v1"),
        importlib.import_module("src.core.economic_command_signature_verifier_registry_v1"),
        importlib.import_module("src.core.economic_command_signature_verifier_deployment_v1"),
        importlib.import_module("src.core.zdex_hyperdeflation_types_v1"),
        importlib.import_module("src.core.global_accounting_allocation_certificate_v1"),
        importlib.import_module("src.core.economic_initial_state_atom_coverage_v1"),
        importlib.import_module("src.core.economic_initial_state_outbox_continuity_v1"),
        importlib.import_module("src.core.managed_asset_policy_registry_v1"),
        importlib.import_module("src.core.perps_margin_types_v1"),
        importlib.import_module("src.core.zdex_tokenomics_lane_v1"),
    ]
    python_twins: dict[str, int] = {}
    for name in rust_bounds:
        for module in twin_modules:
            if hasattr(module, name):
                python_twins[name] = getattr(module, name)
                break
    assert set(python_twins) == set(rust_bounds), (
        sorted(set(rust_bounds) - set(python_twins)),
        sorted(set(python_twins) - set(rust_bounds)),
    )
    assert python_twins == rust_bounds
    assert len(rust_bounds) >= 37
