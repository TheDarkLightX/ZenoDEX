from __future__ import annotations

import pytest

from src.kernels.python.strategy_budget_guard_v1_adapter import (
    StrategyBudgetState,
    consume_order,
    init_state,
    roll_window,
    trigger_kill_switch,
)


def test_consume_order_accepts_in_budget() -> None:
    result = consume_order(
        state=StrategyBudgetState(window_id=1, spent_in_window=100, kill_switch_on=False),
        order_amount=50,
        per_order_limit=100,
        window_budget=500,
    )
    assert result.ok is True
    assert result.state.spent_in_window == 150
    assert result.order_applied is True


def test_consume_order_rejects_per_order_limit() -> None:
    result = consume_order(
        state=init_state(),
        order_amount=101,
        per_order_limit=100,
        window_budget=500,
    )
    assert result.ok is False
    assert result.error == "per_order_limit_exceeded"


def test_consume_order_rejects_window_budget() -> None:
    result = consume_order(
        state=StrategyBudgetState(window_id=1, spent_in_window=480, kill_switch_on=False),
        order_amount=30,
        per_order_limit=100,
        window_budget=500,
    )
    assert result.ok is False
    assert result.error == "window_budget_exceeded"


def test_consume_order_rejects_spent_overflow() -> None:
    result = consume_order(
        state=StrategyBudgetState(window_id=1, spent_in_window=0xFFFFFFFF, kill_switch_on=False),
        order_amount=1,
        per_order_limit=0xFFFFFFFF,
        window_budget=0xFFFFFFFF,
    )
    assert result.ok is False
    assert result.error == "spent_overflow"


def test_consume_order_rejects_when_kill_switch_active() -> None:
    result = consume_order(
        state=StrategyBudgetState(window_id=1, spent_in_window=0, kill_switch_on=True),
        order_amount=30,
        per_order_limit=100,
        window_budget=500,
    )
    assert result.ok is False
    assert result.error == "kill_switch_active"


def test_roll_window_resets_spent_and_advances_id() -> None:
    result = roll_window(
        state=StrategyBudgetState(window_id=4, spent_in_window=300, kill_switch_on=False),
        new_window_id=5,
    )
    assert result.ok is True
    assert result.state.window_id == 5
    assert result.state.spent_in_window == 0


def test_trigger_kill_switch_latches_state() -> None:
    result = trigger_kill_switch(state=StrategyBudgetState(window_id=2, spent_in_window=50, kill_switch_on=False))
    assert result.ok is True
    assert result.state.kill_switch_on is True
    assert result.kill_switch_active is True


def test_budget_adapter_rejects_invalid_state_types_and_ranges() -> None:
    with pytest.raises(TypeError, match="kill_switch_on must be a bool"):
        StrategyBudgetState(window_id=0, spent_in_window=0, kill_switch_on=1)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="window_id out of u32 range"):
        StrategyBudgetState(window_id=-1, spent_in_window=0, kill_switch_on=False)


def test_budget_adapter_rejects_bad_function_inputs() -> None:
    with pytest.raises(TypeError, match="state must be a StrategyBudgetState"):
        consume_order(state="bad", order_amount=1, per_order_limit=1, window_budget=1)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="order_amount must be an int"):
        consume_order(state=init_state(), order_amount=True, per_order_limit=1, window_budget=1)
    with pytest.raises(ValueError, match="order_amount out of u32 range"):
        consume_order(state=init_state(), order_amount=0, per_order_limit=1, window_budget=1)
    with pytest.raises(TypeError, match="state must be a StrategyBudgetState"):
        roll_window(state="bad", new_window_id=1)  # type: ignore[arg-type]
    monotone = roll_window(state=StrategyBudgetState(window_id=2, spent_in_window=0, kill_switch_on=False), new_window_id=2)
    assert monotone.ok is False
    assert monotone.error == "window_id_not_monotone"
    with pytest.raises(TypeError, match="state must be a StrategyBudgetState"):
        trigger_kill_switch(state="bad")  # type: ignore[arg-type]
