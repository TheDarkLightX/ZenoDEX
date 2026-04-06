from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...state.intent_nonce_sender_resolution_gate import evaluate_intent_nonce_sender_resolution_gate

IR_HASH = "sha256:8266ce97d73f5b49b51241b9c82de2d22bec7d39f405008d3ca197858bc0ca3b"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class IntentNonceSenderResolutionGateV1NativeAdapter:
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


def _handle_evaluate_sender_resolution(adapter: IntentNonceSenderResolutionGateV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_sender_resolution"
    try:
        outcome = evaluate_intent_nonce_sender_resolution_gate(
            strict_increasing=s["strict_increasing"],
            contiguous_from_last=s["contiguous_from_last"],
            last_used_nonce=s["last_used_nonce"],
            next_last_nonce=s["next_last_nonce"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    tag_map = {
        "Ok": 0,
        "DuplicateNonce": 1,
        "SequenceInvalid": 2,
    }
    return StepOk(
        state=dict(s),
        effects={
            "sender_ok": bool(outcome.sender_ok),
            "resolved_last_nonce": int(outcome.resolved_last_nonce),
            "reject_tag": int(tag_map[outcome.reject_code]),
        },
    )


def _commit_effect(adapter: IntentNonceSenderResolutionGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[IntentNonceSenderResolutionGateV1NativeAdapter, Any], Any]] = {
    "evaluate_sender_resolution": _handle_evaluate_sender_resolution,
}

EFFECT_HANDLERS: dict[str, Callable[[IntentNonceSenderResolutionGateV1NativeAdapter, str, Any], None]] = {
    "sender_ok": _commit_effect,
    "resolved_last_nonce": _commit_effect,
    "reject_tag": _commit_effect,
}


def make_adapter(ir: Any) -> IntentNonceSenderResolutionGateV1NativeAdapter:
    return IntentNonceSenderResolutionGateV1NativeAdapter(ir=ir)
