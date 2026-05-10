"""Native shell adapter for `perp_tau_ingress_stream_v1`."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.perp_tau_ingress_stream import evaluate_perp_tau_ingress_stream

IR_HASH = "sha256:8854d38ea6cdeadbe58342b9bd1e4b564ff346762f3c45a34a7c9cf69d68ec3e"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class PerpTauIngressStreamV1NativeAdapter:
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


def _handle_select_perp_stream(adapter: PerpTauIngressStreamV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "select_perp_stream"
    try:
        outcome = evaluate_perp_tau_ingress_stream(
            upstream_stream_present=_require_bool_flag("upstream_stream_present", s["upstream_stream_present"]),
            legacy_stream_present=_require_bool_flag("legacy_stream_present", s["legacy_stream_present"]),
            legacy_dex_stream_present=_require_bool_flag("legacy_dex_stream_present", s["legacy_dex_stream_present"]),
            legacy_candidate_dex_like=_require_bool_flag("legacy_candidate_dex_like", s["legacy_candidate_dex_like"]),
            legacy_candidate_perp_like=_require_bool_flag(
                "legacy_candidate_perp_like", s["legacy_candidate_perp_like"]
            ),
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)
    checks = outcome.checks
    return StepOk(
        state=dict(s),
        effects={
            "upstream_stream_selected": bool(outcome.upstream_stream_selected),
            "legacy_fallback_used": bool(outcome.legacy_fallback_used),
            "legacy_dex_conflict": bool(
                (not checks["upstream_stream_present"])
                and checks["legacy_stream_present"]
                and checks["legacy_dex_stream_present"]
            ),
            "legacy_candidate_dex_like": bool(
                (not checks["upstream_stream_present"])
                and checks["legacy_stream_present"]
                and (not checks["legacy_dex_stream_present"])
                and checks["legacy_candidate_dex_like"]
            ),
            "legacy_candidate_perp_like": bool(checks["legacy_stream_present"] and checks["legacy_candidate_perp_like"]),
            "selected": bool(outcome.selected),
            "reject_code": str(outcome.reject_code),
        },
    )


def _commit_effect(adapter: PerpTauIngressStreamV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[PerpTauIngressStreamV1NativeAdapter, Any], Any]] = {
    "select_perp_stream": _handle_select_perp_stream,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpTauIngressStreamV1NativeAdapter, str, Any], None]] = {
    "upstream_stream_selected": _commit_effect,
    "legacy_fallback_used": _commit_effect,
    "legacy_dex_conflict": _commit_effect,
    "legacy_candidate_dex_like": _commit_effect,
    "legacy_candidate_perp_like": _commit_effect,
    "selected": _commit_effect,
    "reject_code": _commit_effect,
}


def make_adapter(ir: Any) -> PerpTauIngressStreamV1NativeAdapter:
    return PerpTauIngressStreamV1NativeAdapter(ir=ir)
