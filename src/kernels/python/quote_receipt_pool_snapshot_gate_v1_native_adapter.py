from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.quote_receipts import evaluate_route_quote_receipt_pool_snapshot_gate

IR_HASH = "sha256:949b5e97b37b637ac3c833806f00b47de4ec0c28edd383f1f54c6f72567d58b0"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class QuoteReceiptPoolSnapshotGateV1NativeAdapter:
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


def _handle_evaluate_route_quote_receipt_pool_snapshot_gate(
    adapter: QuoteReceiptPoolSnapshotGateV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_route_quote_receipt_pool_snapshot_gate"
    try:
        outcome = evaluate_route_quote_receipt_pool_snapshot_gate(
            pool_entries_well_formed=s["pool_entries_well_formed"],
            all_pools_present=s["all_pools_present"],
            all_fingerprints_match=s["all_fingerprints_match"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    tag_map = {
        "Ok": 0,
        "BadPoolFingerprint": 1,
        "MissingPool": 2,
        "PoolSnapshotMismatch": 3,
    }
    return StepOk(
        state=dict(s),
        effects={
            "snapshot_ok": bool(outcome.snapshot_ok),
            "reject_tag": int(tag_map[outcome.reject_code]),
        },
    )


def _commit_effect(adapter: QuoteReceiptPoolSnapshotGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[QuoteReceiptPoolSnapshotGateV1NativeAdapter, Any], Any]] = {
    "evaluate_route_quote_receipt_pool_snapshot_gate": _handle_evaluate_route_quote_receipt_pool_snapshot_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[QuoteReceiptPoolSnapshotGateV1NativeAdapter, str, Any], None]] = {
    "snapshot_ok": _commit_effect,
    "reject_tag": _commit_effect,
}


def make_adapter(ir: Any) -> QuoteReceiptPoolSnapshotGateV1NativeAdapter:
    return QuoteReceiptPoolSnapshotGateV1NativeAdapter(ir=ir)
