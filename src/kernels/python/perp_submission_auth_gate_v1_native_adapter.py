"""Native shell adapter for `perp_submission_auth_gate_v1`."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.perp_submission_auth_gate import evaluate_perp_submission_auth_gate


IR_HASH = "sha256:25564f2b665b70c50d646cd74ef7b6f82ab7d692044f149b3a09e10d2a2347e8"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class PerpSubmissionAuthGateV1NativeAdapter:
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


def _handle_evaluate_submission_auth_gate(adapter: PerpSubmissionAuthGateV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_submission_auth_gate"
    try:
        outcome = evaluate_perp_submission_auth_gate(
            mode_signed=s["mode_signed"],
            mode_sender_bound=s["mode_sender_bound"],
            signed_surface_ok=s["signed_surface_ok"],
            signer_role_set_ok=s["signer_role_set_ok"],
            deadline_ok=s["deadline_ok"],
            nonce_domain_ok=s["nonce_domain_ok"],
            nonce_expected_ok=s["nonce_expected_ok"],
            signature_ok=s["signature_ok"],
            tx_sender_binding_ok=s["tx_sender_binding_ok"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "mode_ok": bool(outcome.mode_ok),
            "relay_allowed": bool(outcome.relay_allowed),
            "consume_nonce": bool(outcome.consume_nonce),
            "admission_ok": bool(outcome.admission_ok),
            "reject_code": str(outcome.reject_code),
        },
    )


def _commit_effect(adapter: PerpSubmissionAuthGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[PerpSubmissionAuthGateV1NativeAdapter, Any], Any]] = {
    "evaluate_submission_auth_gate": _handle_evaluate_submission_auth_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpSubmissionAuthGateV1NativeAdapter, str, Any], None]] = {
    "mode_ok": _commit_effect,
    "relay_allowed": _commit_effect,
    "consume_nonce": _commit_effect,
    "admission_ok": _commit_effect,
    "reject_code": _commit_effect,
}


def make_adapter(ir: Any) -> PerpSubmissionAuthGateV1NativeAdapter:
    return PerpSubmissionAuthGateV1NativeAdapter(ir=ir)
