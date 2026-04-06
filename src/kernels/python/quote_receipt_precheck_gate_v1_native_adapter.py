from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.quote_receipts import evaluate_route_quote_receipt_precheck_gate

IR_HASH = "sha256:639709334ce470302809abab96702899c1f6895931a69c55304a640f6399eb90"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class QuoteReceiptPrecheckGateV1NativeAdapter:
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


def _handle_evaluate_route_quote_receipt_precheck_gate(
    adapter: QuoteReceiptPrecheckGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_route_quote_receipt_precheck_gate"
    try:
        outcome = evaluate_route_quote_receipt_precheck_gate(
            schema_ok=s["schema_ok"],
            receipt_hash_present=s["receipt_hash_present"],
            hash_matches=s["hash_matches"],
            kind_ok=s["kind_ok"],
            canonical_certificate_allowed=s["canonical_certificate_allowed"],
            body_assets_ok=s["body_assets_ok"],
            quote_epoch_ok=s["quote_epoch_ok"],
            pools_object_ok=s["pools_object_ok"],
            legs_list_ok=s["legs_list_ok"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    tag_map = {
        "Ok": 0,
        "BadSchema": 1,
        "MissingReceiptHash": 2,
        "HashMismatch": 3,
        "BadKind": 4,
        "UnexpectedCanonicalRouteCertificate": 5,
        "BadBodyAssets": 6,
        "BadQuoteEpoch": 7,
        "BadPools": 8,
        "BadLegs": 9,
    }
    return StepOk(
        state=dict(s),
        effects={
            "precheck_ok": bool(outcome.precheck_ok),
            "reject_tag": int(tag_map[outcome.reject_code]),
        },
    )


def _commit_effect(adapter: QuoteReceiptPrecheckGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[QuoteReceiptPrecheckGateV1NativeAdapter, Any], Any]] = {
    "evaluate_route_quote_receipt_precheck_gate": _handle_evaluate_route_quote_receipt_precheck_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[QuoteReceiptPrecheckGateV1NativeAdapter, str, Any], None]] = {
    "precheck_ok": _commit_effect,
    "reject_tag": _commit_effect,
}


def make_adapter(ir: Any) -> QuoteReceiptPrecheckGateV1NativeAdapter:
    return QuoteReceiptPrecheckGateV1NativeAdapter(ir=ir)
