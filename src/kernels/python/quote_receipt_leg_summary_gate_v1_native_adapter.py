from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.quote_receipts import evaluate_route_quote_receipt_leg_summary_gate

IR_HASH = "sha256:74b425b0b61eb181955f7a0a5ad65a71bb6cb1b4697b621ed547a44cb2b4bf1f"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class QuoteReceiptLegSummaryGateV1NativeAdapter:
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


def _handle_evaluate_route_quote_receipt_leg_summary_gate(
    adapter: QuoteReceiptLegSummaryGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_route_quote_receipt_leg_summary_gate"
    try:
        outcome = evaluate_route_quote_receipt_leg_summary_gate(
            final_asset_out_ok=s["final_asset_out_ok"],
            first_hop_amount_in_ok=s["first_hop_amount_in_ok"],
            last_hop_amount_out_ok=s["last_hop_amount_out_ok"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    tag_map = {
        "Ok": 0,
        "LegAssetOutMismatch": 1,
        "LegAmountInMismatch": 2,
        "LegAmountOutMismatch": 3,
    }
    return StepOk(
        state=dict(s),
        effects={
            "leg_ok": bool(outcome.leg_ok),
            "reject_tag": int(tag_map[outcome.reject_code]),
        },
    )


def _commit_effect(adapter: QuoteReceiptLegSummaryGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[QuoteReceiptLegSummaryGateV1NativeAdapter, Any], Any]] = {
    "evaluate_route_quote_receipt_leg_summary_gate": _handle_evaluate_route_quote_receipt_leg_summary_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[QuoteReceiptLegSummaryGateV1NativeAdapter, str, Any], None]] = {
    "leg_ok": _commit_effect,
    "reject_tag": _commit_effect,
}


def make_adapter(ir: Any) -> QuoteReceiptLegSummaryGateV1NativeAdapter:
    return QuoteReceiptLegSummaryGateV1NativeAdapter(ir=ir)
