from __future__ import annotations

from dataclasses import dataclass


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


@dataclass(frozen=True)
class StrategyKillSwitchGuardResult:
    ok: bool
    kill_switch_enabled: bool
    kill_switch_active: bool
    error: str | None = None


def check_strategy_kill_switch_guard(
    *,
    kill_switch_enabled: bool,
    kill_switch_active: bool,
) -> StrategyKillSwitchGuardResult:
    kill_switch_enabled = _require_bool("kill_switch_enabled", kill_switch_enabled)
    kill_switch_active = _require_bool("kill_switch_active", kill_switch_active)
    ok = (not kill_switch_enabled) or (not kill_switch_active)
    error = None if ok else "kill_switch_active"
    return StrategyKillSwitchGuardResult(
        ok=ok,
        kill_switch_enabled=kill_switch_enabled,
        kill_switch_active=kill_switch_active,
        error=error,
    )
