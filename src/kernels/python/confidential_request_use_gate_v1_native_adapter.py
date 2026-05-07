from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...state.confidential_requests import evaluate_confidential_request_use_transition

IR_HASH = "sha256:2e8787b1eaa3ece7fb1ae4ab43bb560d9144dbaf67fefbb4857c9c684d9a508b"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class ConfidentialRequestUseGateV1NativeAdapter:
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


def _handle_evaluate_confidential_request_use(
    adapter: ConfidentialRequestUseGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_confidential_request_use"
    try:
        outcome = evaluate_confidential_request_use_transition(
            request_used_before=s["request_used_before"],
            consume_request=s["consume_request"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "request_unused_ok": bool(outcome.request_unused_ok),
            "transition_ok": bool(outcome.transition_ok),
            "consume_applied": bool(outcome.consume_applied),
            "request_used_after": bool(outcome.request_used_after),
        },
    )


def _commit_effect(
    adapter: ConfidentialRequestUseGateV1NativeAdapter,
    effect_id: str,
    value: Any,
) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ConfidentialRequestUseGateV1NativeAdapter, Any], Any]] = {
    "evaluate_confidential_request_use": _handle_evaluate_confidential_request_use,
}

EFFECT_HANDLERS: dict[str, Callable[[ConfidentialRequestUseGateV1NativeAdapter, str, Any], None]] = {
    "request_unused_ok": _commit_effect,
    "transition_ok": _commit_effect,
    "consume_applied": _commit_effect,
    "request_used_after": _commit_effect,
}


def make_adapter(ir: Any) -> ConfidentialRequestUseGateV1NativeAdapter:
    return ConfidentialRequestUseGateV1NativeAdapter(ir=ir)
