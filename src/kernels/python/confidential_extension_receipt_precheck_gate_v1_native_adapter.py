from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.confidential_extension_receipts import (
    evaluate_confidential_extension_receipt_precheck_gate,
)

IR_HASH = "sha256:79186355a37a19a3bb7b1ac511d27b7ee819faadcd16b54c20978123daf6cf3f"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class ConfidentialExtensionReceiptPrecheckGateV1NativeAdapter:
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


def _handle_evaluate_confidential_extension_receipt_precheck_gate(
    adapter: ConfidentialExtensionReceiptPrecheckGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_confidential_extension_receipt_precheck_gate"
    try:
        outcome = evaluate_confidential_extension_receipt_precheck_gate(
            schema_ok=s["schema_ok"],
            receipt_hash_present=s["receipt_hash_present"],
            hash_matches=s["hash_matches"],
            extension_id_ok=s["extension_id_ok"],
            provider_id_ok=s["provider_id_ok"],
            request_id_ok=s["request_id_ok"],
            policy_version_ok=s["policy_version_ok"],
            policy_digest_ok=s["policy_digest_ok"],
            measurement_format_ok=s["measurement_format_ok"],
            measurement_approved=s["measurement_approved"],
            host_object_ok=s["host_object_ok"],
            attestation_object_ok=s["attestation_object_ok"],
            accounting_object_ok=s["accounting_object_ok"],
            numeric_fields_ok=s["numeric_fields_ok"],
            do_execute_flag_ok=s["do_execute_flag_ok"],
            policy_ok_flag_ok=s["policy_ok_flag_ok"],
            nonce_unused_flag_ok=s["nonce_unused_flag_ok"],
            output_bound_ok_flag_ok=s["output_bound_ok_flag_ok"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "precheck_ok": bool(outcome.precheck_ok),
            "reject_tag": int({
                "Ok": 0,
                "BadSchema": 1,
                "MissingReceiptHash": 2,
                "HashMismatch": 3,
                "BadExtensionId": 4,
                "BadProviderId": 5,
                "BadRequestId": 6,
                "BadPolicyVersion": 7,
                "BadPolicyDigest": 8,
                "BadMeasurement": 9,
                "MeasurementNotApproved": 10,
                "BadHost": 11,
                "BadAttestation": 12,
                "BadAccounting": 13,
                "BadNumericField": 14,
                "BadDoExecute": 15,
                "BadPolicyOk": 16,
                "BadNonceUnused": 17,
                "BadOutputBoundOk": 18,
            }[outcome.reject_code]),
        },
    )


def _commit_effect(adapter: ConfidentialExtensionReceiptPrecheckGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ConfidentialExtensionReceiptPrecheckGateV1NativeAdapter, Any], Any]] = {
    "evaluate_confidential_extension_receipt_precheck_gate": _handle_evaluate_confidential_extension_receipt_precheck_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[ConfidentialExtensionReceiptPrecheckGateV1NativeAdapter, str, Any], None]] = {
    "precheck_ok": _commit_effect,
    "reject_tag": _commit_effect,
}


def make_adapter(ir: Any) -> ConfidentialExtensionReceiptPrecheckGateV1NativeAdapter:
    return ConfidentialExtensionReceiptPrecheckGateV1NativeAdapter(ir=ir)
