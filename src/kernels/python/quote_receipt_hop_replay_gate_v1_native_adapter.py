from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.quote_receipts import evaluate_route_quote_receipt_hop_replay_gate

IR_HASH = "sha256:910cd2914e39ec51ee4b7b95cf72c3ba634629601e36d77e8c924a4fea5d8176"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class QuoteReceiptHopReplayGateV1NativeAdapter:
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


def _handle_evaluate_route_quote_receipt_hop_replay_gate(
    adapter: QuoteReceiptHopReplayGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_route_quote_receipt_hop_replay_gate"
    try:
        outcome = evaluate_route_quote_receipt_hop_replay_gate(
            direction_ok=s["direction_ok"],
            forward_direction=s["forward_direction"],
            swap_ok=s["swap_ok"],
            quote_matches=s["quote_matches"],
            next_reserve_in=s["next_reserve_in"],
            next_reserve_out=s["next_reserve_out"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    tag_map = {
        "Ok": 0,
        "BadPoolDirection": 1,
        "HopQuoteError": 2,
        "HopQuoteMismatch": 3,
    }
    return StepOk(
        state=dict(s),
        effects={
            "replay_ok": bool(outcome.replay_ok),
            "reject_tag": int(tag_map[outcome.reject_code]),
            "next_reserve0": int(outcome.next_reserve0),
            "next_reserve1": int(outcome.next_reserve1),
        },
    )


def _commit_effect(adapter: QuoteReceiptHopReplayGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[QuoteReceiptHopReplayGateV1NativeAdapter, Any], Any]] = {
    "evaluate_route_quote_receipt_hop_replay_gate": _handle_evaluate_route_quote_receipt_hop_replay_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[QuoteReceiptHopReplayGateV1NativeAdapter, str, Any], None]] = {
    "replay_ok": _commit_effect,
    "reject_tag": _commit_effect,
    "next_reserve0": _commit_effect,
    "next_reserve1": _commit_effect,
}


def make_adapter(ir: Any) -> QuoteReceiptHopReplayGateV1NativeAdapter:
    return QuoteReceiptHopReplayGateV1NativeAdapter(ir=ir)
