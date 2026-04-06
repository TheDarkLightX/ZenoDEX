"""Native shell adapter for `perp_clearinghouse_market_params_guard_v1`."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.perp_clearinghouse_market_params_guard import (
    evaluate_perp_clearinghouse_market_params_guard,
)


IR_HASH = "sha256:1ed863d06f8ba90e77e2aac75258bac1cf14988d0afdf0ef0638fe1680e454eb"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class PerpClearinghouseMarketParamsGuardV1NativeAdapter:
    ir: Any
    _state: dict[str, Any] = field(default_factory=dict)
    _pending_effects: dict[str, Any] = field(default_factory=dict)

    def reset(self, *, state: Mapping[str, Any]) -> None:
        self._state = dict(state)
        self._pending_effects = {}

    def get_state(self) -> Mapping[str, Any]:
        return dict(self._state)

    def apply(self, command: Any) -> Any:
        self._pending_effects = {}
        handler = ACTION_HANDLERS.get(str(getattr(command, "tag", "")))
        if handler is None:
            from ESSO.kernel.interpreter import StepError

            return StepError(code="UnknownAction", message="no handler for command.tag")

        res = handler(self, command)
        from ESSO.kernel.interpreter import StepOk

        if isinstance(res, StepOk):
            self._state = dict(res.state)
            for eff_id, value in res.effects.items():
                eff_handler = EFFECT_HANDLERS.get(str(eff_id))
                if eff_handler is None:
                    continue
                eff_handler(self, str(eff_id), value)
        return res

    def drain_effects(self) -> Mapping[str, Any]:
        out = dict(self._pending_effects)
        self._pending_effects = {}
        return out


def _require_bool_flag(name: str, value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, int) and not isinstance(value, bool) and value in (0, 1):
        return bool(value)
    raise TypeError(f"{name} must be a bool-like 0/1 flag")


def _require_int(name: str, value: Any) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _handle_evaluate_clearinghouse_market_params_guard(
    adapter: PerpClearinghouseMarketParamsGuardV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk

    del command
    s = adapter._state
    action_id = "evaluate_clearinghouse_market_params_guard"
    try:
        outcome = evaluate_perp_clearinghouse_market_params_guard(
            market_kind=_require_int("market_kind", s["market_kind"]),
            operator_ok=_require_bool_flag("operator_ok", s["operator_ok"]),
            epoch_settled_ok=_require_bool_flag("epoch_settled_ok", s["epoch_settled_ok"]),
            position_base_a=_require_int("position_base_a", s["position_base_a"]),
            position_base_b=_require_int("position_base_b", s["position_base_b"]),
            position_base_c=_require_int("position_base_c", s["position_base_c"]),
            old_liquidation_penalty_bps=_require_int(
                "old_liquidation_penalty_bps",
                s["old_liquidation_penalty_bps"],
            ),
            new_liquidation_penalty_bps=_require_int(
                "new_liquidation_penalty_bps",
                s["new_liquidation_penalty_bps"],
            ),
            new_maintenance_margin_bps=_require_int(
                "new_maintenance_margin_bps",
                s["new_maintenance_margin_bps"],
            ),
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "market_kind_ok": bool(outcome.market_kind_ok),
            "positions_open": bool(outcome.positions_open),
            "penalty_increase_ok": bool(outcome.penalty_increase_ok),
            "penalty_below_maintenance_ok": bool(outcome.penalty_below_maintenance_ok),
            "admission_ok": bool(outcome.admission_ok),
            "reject_code": str(outcome.reject_code),
        },
    )


def _commit_effect(adapter: PerpClearinghouseMarketParamsGuardV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[PerpClearinghouseMarketParamsGuardV1NativeAdapter, Any], Any]] = {
    "evaluate_clearinghouse_market_params_guard": _handle_evaluate_clearinghouse_market_params_guard,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpClearinghouseMarketParamsGuardV1NativeAdapter, str, Any], None]] = {
    "market_kind_ok": _commit_effect,
    "positions_open": _commit_effect,
    "penalty_increase_ok": _commit_effect,
    "penalty_below_maintenance_ok": _commit_effect,
    "admission_ok": _commit_effect,
    "reject_code": _commit_effect,
}


def make_adapter(ir: Any) -> PerpClearinghouseMarketParamsGuardV1NativeAdapter:
    return PerpClearinghouseMarketParamsGuardV1NativeAdapter(ir=ir)
