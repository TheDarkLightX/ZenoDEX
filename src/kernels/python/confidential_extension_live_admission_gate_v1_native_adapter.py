from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.confidential_extension_live_admission import (
    evaluate_confidential_extension_live_admission_gate,
)

IR_HASH = "sha256:38268e53a15d6334bfbb784202c0fc5877c23319660454245952755b3436f285"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class ConfidentialExtensionLiveAdmissionGateV1NativeAdapter:
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


def _handle_evaluate_confidential_extension_live_admission(
    adapter: ConfidentialExtensionLiveAdmissionGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_confidential_extension_live_admission"
    try:
        outcome = evaluate_confidential_extension_live_admission_gate(
            do_execute=s["do_execute"],
            receipt_verified=s["receipt_verified"],
            policy_digest_match=s["policy_digest_match"],
            request_used_before=s["request_used_before"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "do_execute_ok": bool(outcome.do_execute_ok),
            "receipt_verified_ok": bool(outcome.receipt_verified_ok),
            "policy_digest_match_ok": bool(outcome.policy_digest_match_ok),
            "request_unused_ok": bool(outcome.request_unused_ok),
            "request_used_after": bool(outcome.request_used_after),
            "admission_ok": bool(outcome.admission_ok),
        },
    )


def _commit_effect(
    adapter: ConfidentialExtensionLiveAdmissionGateV1NativeAdapter,
    effect_id: str,
    value: Any,
) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ConfidentialExtensionLiveAdmissionGateV1NativeAdapter, Any], Any]] = {
    "evaluate_confidential_extension_live_admission": _handle_evaluate_confidential_extension_live_admission,
}

EFFECT_HANDLERS: dict[str, Callable[[ConfidentialExtensionLiveAdmissionGateV1NativeAdapter, str, Any], None]] = {
    "do_execute_ok": _commit_effect,
    "receipt_verified_ok": _commit_effect,
    "policy_digest_match_ok": _commit_effect,
    "request_unused_ok": _commit_effect,
    "request_used_after": _commit_effect,
    "admission_ok": _commit_effect,
}


def make_adapter(ir: Any) -> ConfidentialExtensionLiveAdmissionGateV1NativeAdapter:
    return ConfidentialExtensionLiveAdmissionGateV1NativeAdapter(ir=ir)
