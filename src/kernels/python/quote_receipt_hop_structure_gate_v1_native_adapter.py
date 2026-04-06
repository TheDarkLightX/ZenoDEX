from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.quote_receipts import evaluate_route_quote_receipt_hop_structure_gate

IR_HASH = "sha256:69dcf2a10f37b80f79146475864703c4afc12133e4b2a48472a05162ebacf5ec"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class QuoteReceiptHopStructureGateV1NativeAdapter:
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


def _handle_evaluate_route_quote_receipt_hop_structure_gate(
    adapter: QuoteReceiptHopStructureGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_route_quote_receipt_hop_structure_gate"
    try:
        outcome = evaluate_route_quote_receipt_hop_structure_gate(
            hop_dict_ok=s["hop_dict_ok"],
            pool_id_ok=s["pool_id_ok"],
            snapshotted_pool_present=s["snapshotted_pool_present"],
            working_pool_present=s["working_pool_present"],
            assets_shaped_ok=s["assets_shaped_ok"],
            is_first_hop=s["is_first_hop"],
            first_hop_asset_in_ok=s["first_hop_asset_in_ok"],
            hop_asset_chain_ok=s["hop_asset_chain_ok"],
            hop_amounts_ok=s["hop_amounts_ok"],
            hop_amount_chain_ok=s["hop_amount_chain_ok"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    tag_map = {
        "Ok": 0,
        "BadHop": 1,
        "BadPoolId": 2,
        "MissingPoolFingerprint": 3,
        "MissingWorkingPool": 4,
        "BadAssets": 5,
        "LegAssetInMismatch": 6,
        "HopAssetChainMismatch": 7,
        "BadHopAmounts": 8,
        "HopChainMismatch": 9,
    }
    return StepOk(
        state=dict(s),
        effects={
            "hop_ok": bool(outcome.hop_ok),
            "reject_tag": int(tag_map[outcome.reject_code]),
        },
    )


def _commit_effect(adapter: QuoteReceiptHopStructureGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[QuoteReceiptHopStructureGateV1NativeAdapter, Any], Any]] = {
    "evaluate_route_quote_receipt_hop_structure_gate": _handle_evaluate_route_quote_receipt_hop_structure_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[QuoteReceiptHopStructureGateV1NativeAdapter, str, Any], None]] = {
    "hop_ok": _commit_effect,
    "reject_tag": _commit_effect,
}


def make_adapter(ir: Any) -> QuoteReceiptHopStructureGateV1NativeAdapter:
    return QuoteReceiptHopStructureGateV1NativeAdapter(ir=ir)
