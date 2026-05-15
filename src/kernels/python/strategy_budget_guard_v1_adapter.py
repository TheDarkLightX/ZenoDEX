from __future__ import annotations

from dataclasses import dataclass

MAX_U32 = 0xFFFFFFFF


def _require_u32(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > MAX_U32:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


@dataclass(frozen=True)
class StrategyBudgetState:
    window_id: int = 0
    spent_in_window: int = 0
    kill_switch_on: bool = False

    def __post_init__(self) -> None:
        object.__setattr__(self, "window_id", _require_u32("window_id", self.window_id))
        object.__setattr__(self, "spent_in_window", _require_u32("spent_in_window", self.spent_in_window))
        if not isinstance(self.kill_switch_on, bool):
            raise TypeError("kill_switch_on must be a bool")


@dataclass(frozen=True)
class StrategyBudgetResult:
    ok: bool
    state: StrategyBudgetState
    budget_ok: bool
    kill_switch_active: bool
    order_applied: bool
    error: str | None = None


def init_state() -> StrategyBudgetState:
    return StrategyBudgetState()


def consume_order(
    *,
    state: StrategyBudgetState,
    order_amount: int,
    per_order_limit: int,
    window_budget: int,
) -> StrategyBudgetResult:
    if not isinstance(state, StrategyBudgetState):
        raise TypeError("state must be a StrategyBudgetState")
    order_amount = _require_u32("order_amount", order_amount, minimum=1)
    per_order_limit = _require_u32("per_order_limit", per_order_limit, minimum=1)
    window_budget = _require_u32("window_budget", window_budget, minimum=1)
    if state.kill_switch_on:
        return StrategyBudgetResult(
            ok=False,
            state=state,
            budget_ok=False,
            kill_switch_active=True,
            order_applied=False,
            error="kill_switch_active",
        )
    if order_amount > per_order_limit:
        return StrategyBudgetResult(
            ok=False,
            state=state,
            budget_ok=False,
            kill_switch_active=False,
            order_applied=False,
            error="per_order_limit_exceeded",
        )
    spent_after = state.spent_in_window + order_amount
    if spent_after > MAX_U32:
        return StrategyBudgetResult(
            ok=False,
            state=state,
            budget_ok=False,
            kill_switch_active=False,
            order_applied=False,
            error="spent_overflow",
        )
    if spent_after > window_budget:
        return StrategyBudgetResult(
            ok=False,
            state=state,
            budget_ok=False,
            kill_switch_active=False,
            order_applied=False,
            error="window_budget_exceeded",
        )
    next_state = StrategyBudgetState(
        window_id=state.window_id,
        spent_in_window=spent_after,
        kill_switch_on=False,
    )
    return StrategyBudgetResult(
        ok=True,
        state=next_state,
        budget_ok=True,
        kill_switch_active=False,
        order_applied=True,
    )


def roll_window(*, state: StrategyBudgetState, new_window_id: int) -> StrategyBudgetResult:
    if not isinstance(state, StrategyBudgetState):
        raise TypeError("state must be a StrategyBudgetState")
    new_window_id = _require_u32("new_window_id", new_window_id)
    if new_window_id <= state.window_id:
        return StrategyBudgetResult(
            ok=False,
            state=state,
            budget_ok=False,
            kill_switch_active=state.kill_switch_on,
            order_applied=False,
            error="window_id_not_monotone",
        )
    next_state = StrategyBudgetState(window_id=new_window_id, spent_in_window=0, kill_switch_on=state.kill_switch_on)
    return StrategyBudgetResult(
        ok=True,
        state=next_state,
        budget_ok=True,
        kill_switch_active=next_state.kill_switch_on,
        order_applied=False,
    )


def trigger_kill_switch(*, state: StrategyBudgetState) -> StrategyBudgetResult:
    if not isinstance(state, StrategyBudgetState):
        raise TypeError("state must be a StrategyBudgetState")
    next_state = StrategyBudgetState(
        window_id=state.window_id,
        spent_in_window=state.spent_in_window,
        kill_switch_on=True,
    )
    return StrategyBudgetResult(
        ok=True,
        state=next_state,
        budget_ok=False,
        kill_switch_active=True,
        order_applied=False,
    )
