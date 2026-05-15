from __future__ import annotations

from dataclasses import dataclass


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


@dataclass(frozen=True)
class StrategyDecisionKernelResult:
    ok: bool
    winner_index: int
    winner_key: int
    emit_requested: bool
    emit_admissible: bool
    error: str | None = None


def check_strategy_decision_kernel(
    *,
    emit_requested: bool,
    emit_admissible: bool,
) -> StrategyDecisionKernelResult:
    emit_requested = _require_bool("emit_requested", emit_requested)
    emit_admissible = _require_bool("emit_admissible", emit_admissible)
    emit_key = 1 if emit_requested and emit_admissible else 0
    noop_key = 0
    winner_index = 1 if emit_key > noop_key else 0
    winner_key = emit_key if winner_index == 1 else noop_key
    return StrategyDecisionKernelResult(
        ok=True,
        winner_index=winner_index,
        winner_key=winner_key,
        emit_requested=emit_requested,
        emit_admissible=emit_admissible,
        error=None,
    )
