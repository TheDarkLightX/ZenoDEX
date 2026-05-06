from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.confidential_extension_receipts import (
    evaluate_confidential_extension_receipt_gate,
)

IR_HASH = "sha256:f1c91a81414d061d10332a77d5aa865a78aec221a2c3a56391c0b036c20b3943"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class ConfidentialExtensionReceiptGateV1NativeAdapter:
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


def _handle_evaluate_confidential_extension_receipt_gate(
    adapter: ConfidentialExtensionReceiptGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_confidential_extension_receipt_gate"
    try:
        outcome = evaluate_confidential_extension_receipt_gate(
            do_execute=s["do_execute"],
            policy_ok=s["policy_ok"],
            nonce_unused=s["nonce_unused"],
            output_bound_ok=s["output_bound_ok"],
            current_epoch=s["current_epoch"],
            attestation_epoch=s["attestation_epoch"],
            max_attestation_age=s["max_attestation_age"],
            fee_charged=s["fee_charged"],
            receipt_fee=s["receipt_fee"],
            credit_before=s["credit_before"],
            credit_after=s["credit_after"],
            provider_balance_before=s["provider_balance_before"],
            provider_balance_after=s["provider_balance_after"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "fresh_attestation_ok": bool(outcome.fresh_attestation_ok),
            "host_guards_ok": bool(outcome.host_guards_ok),
            "accounting_ok": bool(outcome.accounting_ok),
            "receipt_admissible": bool(outcome.receipt_admissible),
        },
    )


def _commit_effect(
    adapter: ConfidentialExtensionReceiptGateV1NativeAdapter,
    effect_id: str,
    value: Any,
) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ConfidentialExtensionReceiptGateV1NativeAdapter, Any], Any]] = {
    "evaluate_confidential_extension_receipt_gate": _handle_evaluate_confidential_extension_receipt_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[ConfidentialExtensionReceiptGateV1NativeAdapter, str, Any], None]] = {
    "fresh_attestation_ok": _commit_effect,
    "host_guards_ok": _commit_effect,
    "accounting_ok": _commit_effect,
    "receipt_admissible": _commit_effect,
}


def make_adapter(ir: Any) -> ConfidentialExtensionReceiptGateV1NativeAdapter:
    return ConfidentialExtensionReceiptGateV1NativeAdapter(ir=ir)
