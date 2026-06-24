from __future__ import annotations

import ast
import inspect
from typing import Any, cast

import pytest

from src.kernels.python import strategy_execution_guard_v1_adapter
from src.kernels.python.strategy_execution_guard_v1_adapter import check_order_execution


def test_check_order_execution_accepts_valid_submission() -> None:
    result = check_order_execution(
        current_epoch=10,
        valid_from_epoch=1,
        valid_until_epoch=100,
        last_action_epoch=5,
        cadence_epochs=4,
        min_order_spacing_epochs=2,
        projected_live_orders=2,
        max_live_orders=3,
    )
    assert result.ok is True
    assert result.error is None


def test_check_order_execution_skips_before_window() -> None:
    result = check_order_execution(
        current_epoch=0,
        valid_from_epoch=1,
        valid_until_epoch=100,
        last_action_epoch=None,
        cadence_epochs=4,
        min_order_spacing_epochs=0,
        projected_live_orders=1,
        max_live_orders=3,
    )
    assert result.ok is False
    assert result.error == "strategy_window_not_open:0<1"


def test_check_order_execution_skips_after_window() -> None:
    result = check_order_execution(
        current_epoch=101,
        valid_from_epoch=1,
        valid_until_epoch=100,
        last_action_epoch=None,
        cadence_epochs=4,
        min_order_spacing_epochs=0,
        projected_live_orders=1,
        max_live_orders=3,
    )
    assert result.ok is False
    assert result.error == "strategy_window_expired:101>100"


def test_check_order_execution_rejects_non_monotone_epoch() -> None:
    result = check_order_execution(
        current_epoch=4,
        valid_from_epoch=1,
        valid_until_epoch=100,
        last_action_epoch=5,
        cadence_epochs=4,
        min_order_spacing_epochs=0,
        projected_live_orders=1,
        max_live_orders=3,
    )
    assert result.ok is False
    assert result.error == "non_monotone_epoch:4<5"


def test_check_order_execution_skips_when_cadence_not_elapsed() -> None:
    result = check_order_execution(
        current_epoch=7,
        valid_from_epoch=1,
        valid_until_epoch=100,
        last_action_epoch=5,
        cadence_epochs=4,
        min_order_spacing_epochs=1,
        projected_live_orders=1,
        max_live_orders=3,
    )
    assert result.ok is False
    assert result.error == "cadence_not_elapsed:delta=2,required=4"


def test_check_order_execution_skips_when_min_spacing_not_elapsed() -> None:
    result = check_order_execution(
        current_epoch=7,
        valid_from_epoch=1,
        valid_until_epoch=100,
        last_action_epoch=5,
        cadence_epochs=1,
        min_order_spacing_epochs=3,
        projected_live_orders=1,
        max_live_orders=3,
    )
    assert result.ok is False
    assert result.error == "cadence_not_elapsed:delta=2,required=3"


def test_check_order_execution_skips_when_live_order_cap_would_be_exceeded() -> None:
    result = check_order_execution(
        current_epoch=10,
        valid_from_epoch=1,
        valid_until_epoch=100,
        last_action_epoch=None,
        cadence_epochs=4,
        min_order_spacing_epochs=0,
        projected_live_orders=4,
        max_live_orders=3,
    )
    assert result.ok is False
    assert result.error == "max_live_orders_reached:4>3"


def test_check_order_execution_rejects_invalid_ranges_and_types() -> None:
    with pytest.raises(ValueError, match="valid_from_epoch must be <="):
        check_order_execution(
            current_epoch=10,
            valid_from_epoch=5,
            valid_until_epoch=4,
            last_action_epoch=None,
            cadence_epochs=4,
            min_order_spacing_epochs=0,
            projected_live_orders=1,
            max_live_orders=3,
        )
    with pytest.raises(TypeError, match="current_epoch must be an int"):
        check_order_execution(
            current_epoch=cast(Any, "10"),
            valid_from_epoch=1,
            valid_until_epoch=100,
            last_action_epoch=None,
            cadence_epochs=4,
            min_order_spacing_epochs=0,
            projected_live_orders=1,
            max_live_orders=3,
        )
    with pytest.raises(ValueError, match="current_epoch out of u32 range"):
        check_order_execution(
            current_epoch=-1,
            valid_from_epoch=1,
            valid_until_epoch=100,
            last_action_epoch=None,
            cadence_epochs=4,
            min_order_spacing_epochs=0,
            projected_live_orders=1,
            max_live_orders=3,
        )


def test_strategy_execution_guard_adapter_has_no_strippable_asserts() -> None:
    tree = ast.parse(inspect.getsource(strategy_execution_guard_v1_adapter))
    assert not [node for node in ast.walk(tree) if isinstance(node, ast.Assert)]
