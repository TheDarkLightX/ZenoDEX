from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...state.intent_nonce_batch_policy_gate import evaluate_intent_nonce_batch_policy_gate

IR_HASH = "sha256:243286ec5056edaafc28388ea16d0818d191a3c8e5a47a1e769e64508456f6eb"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class IntentNonceBatchPolicyGateV1NativeAdapter:
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


def _handle_evaluate_batch_policy(adapter: IntentNonceBatchPolicyGateV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_batch_policy"
    try:
        outcome = evaluate_intent_nonce_batch_policy_gate(
            empty_batch=s["empty_batch"],
            require_all_nonces=s["require_all_nonces"],
            saw_nonce=s["saw_nonce"],
            saw_missing=s["saw_missing"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    tag_map = {
        "OkProceed": 0,
        "OkCopy": 1,
        "MissingInvalidNonce": 2,
        "MixedPresence": 3,
    }
    return StepOk(
        state=dict(s),
        effects={
            "batch_ok": bool(outcome.batch_ok),
            "return_copy": bool(outcome.return_copy),
            "reject_tag": int(tag_map[outcome.reject_code]),
        },
    )


def _commit_effect(adapter: IntentNonceBatchPolicyGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[IntentNonceBatchPolicyGateV1NativeAdapter, Any], Any]] = {
    "evaluate_batch_policy": _handle_evaluate_batch_policy,
}

EFFECT_HANDLERS: dict[str, Callable[[IntentNonceBatchPolicyGateV1NativeAdapter, str, Any], None]] = {
    "batch_ok": _commit_effect,
    "return_copy": _commit_effect,
    "reject_tag": _commit_effect,
}


def make_adapter(ir: Any) -> IntentNonceBatchPolicyGateV1NativeAdapter:
    return IntentNonceBatchPolicyGateV1NativeAdapter(ir=ir)
