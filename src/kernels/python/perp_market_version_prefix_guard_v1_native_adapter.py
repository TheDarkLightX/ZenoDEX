"""Native shell adapter for `perp_market_version_prefix_guard_v1`."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.perp_market_version_prefix_guard import evaluate_perp_market_version_prefix_guard


IR_HASH = "sha256:c8e4924ab8c14e00ca170421d18d85b8e53c3292353fc335fb3736adcb64608a"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class PerpMarketVersionPrefixGuardV1NativeAdapter:
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
            from ESSO.kernel.interpreter import StepError  # type: ignore

            return StepError(code="UnknownAction", message="no handler for command.tag")

        res = handler(self, command)
        from ESSO.kernel.interpreter import StepOk  # type: ignore

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


def _handle_check_market_version_prefix_guard(adapter: PerpMarketVersionPrefixGuardV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "check_market_version_prefix_guard"
    try:
        outcome = evaluate_perp_market_version_prefix_guard(
            version_is_v0_1=_require_bool_flag("version_is_v0_1", s["version_is_v0_1"]),
            version_is_ch2p=_require_bool_flag("version_is_ch2p", s["version_is_ch2p"]),
            version_is_ch3p=_require_bool_flag("version_is_ch3p", s["version_is_ch3p"]),
            market_has_ch2p_prefix=_require_bool_flag("market_has_ch2p_prefix", s["market_has_ch2p_prefix"]),
            market_has_ch3p_prefix=_require_bool_flag("market_has_ch3p_prefix", s["market_has_ch3p_prefix"]),
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "version_ok": bool(outcome.version_ok),
            "isolated_version": bool(outcome.isolated_version),
            "clearinghouse_2p_version": bool(outcome.clearinghouse_2p_version),
            "clearinghouse_3p_version": bool(outcome.clearinghouse_3p_version),
            "market_prefix_ok": bool(outcome.market_prefix_ok),
            "admission_ok": bool(outcome.admission_ok),
            "reject_code": str(outcome.reject_code),
        },
    )


def _commit_effect(adapter: PerpMarketVersionPrefixGuardV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[PerpMarketVersionPrefixGuardV1NativeAdapter, Any], Any]] = {
    "check_market_version_prefix_guard": _handle_check_market_version_prefix_guard,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpMarketVersionPrefixGuardV1NativeAdapter, str, Any], None]] = {
    "version_ok": _commit_effect,
    "isolated_version": _commit_effect,
    "clearinghouse_2p_version": _commit_effect,
    "clearinghouse_3p_version": _commit_effect,
    "market_prefix_ok": _commit_effect,
    "admission_ok": _commit_effect,
    "reject_code": _commit_effect,
}


def make_adapter(ir: Any) -> PerpMarketVersionPrefixGuardV1NativeAdapter:
    return PerpMarketVersionPrefixGuardV1NativeAdapter(ir=ir)
