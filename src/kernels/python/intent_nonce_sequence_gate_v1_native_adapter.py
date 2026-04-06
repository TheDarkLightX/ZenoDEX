from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...state.intent_nonce_sequence_gate import evaluate_sorted_intent_nonce_sequence_gate

IR_HASH = "sha256:977fe4c5afe39626cedc96d5ee5fa740c9d73ec0b646fe6e76b01fce11b17104"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class IntentNonceSequenceGateV1NativeAdapter:
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


def _handle_evaluate_nonce_sequence(
    adapter: IntentNonceSequenceGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_nonce_sequence"
    try:
        outcome = evaluate_sorted_intent_nonce_sequence_gate(
            last_used_nonce=s["last_used_nonce"],
            nonce_count=s["nonce_count"],
            nonce_0=s["nonce_0"],
            nonce_1=s["nonce_1"],
            nonce_2=s["nonce_2"],
            nonce_3=s["nonce_3"],
            nonce_4=s["nonce_4"],
            nonce_5=s["nonce_5"],
            nonce_6=s["nonce_6"],
            nonce_7=s["nonce_7"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "strict_increasing": bool(outcome.strict_increasing),
            "contiguous_from_last": bool(outcome.contiguous_from_last),
            "sequence_ok": bool(outcome.sequence_ok),
            "next_last_nonce": int(outcome.next_last_nonce),
        },
    )


def _commit_effect(adapter: IntentNonceSequenceGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[IntentNonceSequenceGateV1NativeAdapter, Any], Any]] = {
    "evaluate_nonce_sequence": _handle_evaluate_nonce_sequence,
}

EFFECT_HANDLERS: dict[str, Callable[[IntentNonceSequenceGateV1NativeAdapter, str, Any], None]] = {
    "strict_increasing": _commit_effect,
    "contiguous_from_last": _commit_effect,
    "sequence_ok": _commit_effect,
    "next_last_nonce": _commit_effect,
}


def make_adapter(ir: Any) -> IntentNonceSequenceGateV1NativeAdapter:
    return IntentNonceSequenceGateV1NativeAdapter(ir=ir)
