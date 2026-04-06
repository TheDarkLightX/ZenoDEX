from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.quote_receipts import evaluate_route_quote_receipt_certificate_gate

IR_HASH = "sha256:8c0a6fff72a901c21480d895b792dbe4b6f8d3f6f72b271d42be035a33770bb9"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class QuoteReceiptCertificateGateV1NativeAdapter:
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


def _handle_evaluate_route_quote_receipt_certificate_gate(
    adapter: QuoteReceiptCertificateGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_route_quote_receipt_certificate_gate"
    try:
        outcome = evaluate_route_quote_receipt_certificate_gate(
            cert_present=s["cert_present"],
            cert_dict_ok=s["cert_dict_ok"],
            winner_quote_dict_ok=s["winner_quote_dict_ok"],
            asset_in_match=s["asset_in_match"],
            asset_out_match=s["asset_out_match"],
            amount_in_match=s["amount_in_match"],
            amount_out_match=s["amount_out_match"],
            legs_match=s["legs_match"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    tag_map = {
        "Ok": 0,
        "BadCertificateType": 1,
        "BadWinnerQuote": 2,
        "AssetInMismatch": 3,
        "AssetOutMismatch": 4,
        "AmountInMismatch": 5,
        "AmountOutMismatch": 6,
        "LegsMismatch": 7,
    }
    return StepOk(
        state=dict(s),
        effects={
            "certificate_ok": bool(outcome.certificate_ok),
            "reject_tag": int(tag_map[outcome.reject_code]),
        },
    )


def _commit_effect(adapter: QuoteReceiptCertificateGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[QuoteReceiptCertificateGateV1NativeAdapter, Any], Any]] = {
    "evaluate_route_quote_receipt_certificate_gate": _handle_evaluate_route_quote_receipt_certificate_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[QuoteReceiptCertificateGateV1NativeAdapter, str, Any], None]] = {
    "certificate_ok": _commit_effect,
    "reject_tag": _commit_effect,
}


def make_adapter(ir: Any) -> QuoteReceiptCertificateGateV1NativeAdapter:
    return QuoteReceiptCertificateGateV1NativeAdapter(ir=ir)
