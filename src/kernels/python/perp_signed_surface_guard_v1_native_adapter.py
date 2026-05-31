"""Native shell adapter for `perp_signed_surface_guard_v1`."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.perp_signed_surface_guard import evaluate_perp_signed_surface_guard


IR_HASH = "sha256:04536693a9c6ce4a9d0ce3f88c5da4d79c511eda42d8172825017d32ad881430"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class PerpSignedSurfaceGuardV1NativeAdapter:
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


def _handle_evaluate_signed_surface_guard(adapter: PerpSignedSurfaceGuardV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk

    del command
    s = adapter._state
    action_id = "evaluate_signed_surface_guard"
    try:
        outcome = evaluate_perp_signed_surface_guard(
            action_kind=s["action_kind"],
            version_ok=s["version_ok"],
            unknown_fields_ok=s["unknown_fields_ok"],
            distinct_accounts_ok=s["distinct_accounts_ok"],
            market_accounts_match_ok=s["market_accounts_match_ok"],
            net_zero_ok=s["net_zero_ok"],
            idle_leg_ok=s["idle_leg_ok"],
            positive_price_ok=s["positive_price_ok"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "action_known": bool(outcome.action_known),
            "version_ok": bool(outcome.version_ok),
            "unknown_fields_ok": bool(outcome.unknown_fields_ok),
            "distinct_accounts_ok": bool(outcome.distinct_accounts_ok),
            "market_accounts_match_ok": bool(outcome.market_accounts_match_ok),
            "net_zero_ok": bool(outcome.net_zero_ok),
            "idle_leg_ok": bool(outcome.idle_leg_ok),
            "positive_price_ok": bool(outcome.positive_price_ok),
            "signed_surface_ok": bool(outcome.signed_surface_ok),
            "reject_code": str(outcome.reject_code),
        },
    )


def _commit_effect(adapter: PerpSignedSurfaceGuardV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[PerpSignedSurfaceGuardV1NativeAdapter, Any], Any]] = {
    "evaluate_signed_surface_guard": _handle_evaluate_signed_surface_guard,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpSignedSurfaceGuardV1NativeAdapter, str, Any], None]] = {
    "action_known": _commit_effect,
    "version_ok": _commit_effect,
    "unknown_fields_ok": _commit_effect,
    "distinct_accounts_ok": _commit_effect,
    "market_accounts_match_ok": _commit_effect,
    "net_zero_ok": _commit_effect,
    "idle_leg_ok": _commit_effect,
    "positive_price_ok": _commit_effect,
    "signed_surface_ok": _commit_effect,
    "reject_code": _commit_effect,
}


def make_adapter(ir: Any) -> PerpSignedSurfaceGuardV1NativeAdapter:
    return PerpSignedSurfaceGuardV1NativeAdapter(ir=ir)
