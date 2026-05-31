"""Native (non-interpreter) shell adapter for `perp_apply_funding_auto_gate_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/perp_apply_funding_auto_gate_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/perp_apply_funding_auto_gate_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.perp_apply_funding_auto_gate import evaluate_perp_apply_funding_auto_gate


# Derived from:
# `python3 -m ESSO validate src/kernels/dex/perp_apply_funding_auto_gate_v1.yaml`.
IR_HASH = "sha256:162e2496d744f55b4027802190753e64983ca4fa2cc67166c010e0e266d14a7b"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class PerpApplyFundingAutoGateV1NativeAdapter:
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


def _handle_evaluate_apply_funding_auto_gate(adapter: PerpApplyFundingAutoGateV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_apply_funding_auto_gate"
    try:
        outcome = evaluate_perp_apply_funding_auto_gate(
            now_epoch=s["now_epoch"],
            clearing_price_seen=s["clearing_price_seen"],
            clearing_price_epoch=s["clearing_price_epoch"],
            oracle_last_update_epoch=s["oracle_last_update_epoch"],
            oracle_seen=s["oracle_seen"],
            index_price_e8=s["index_price_e8"],
            max_oracle_staleness_epochs=s["max_oracle_staleness_epochs"],
            clearing_price_e8=s["clearing_price_e8"],
            max_oracle_move_bps=s["max_oracle_move_bps"],
            funding_cap_bps=s["funding_cap_bps"],
            projected_net_funding_quote=s["projected_net_funding_quote"],
            any_funding_applied_this_epoch=s["any_funding_applied_this_epoch"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "clearing_price_seen_ok": bool(outcome.clearing_price_seen_ok),
            "clearing_price_epoch_ok": bool(outcome.clearing_price_epoch_ok),
            "pre_settlement_window_ok": bool(outcome.pre_settlement_window_ok),
            "oracle_seen_ok": bool(outcome.oracle_seen_ok),
            "index_price_ok": bool(outcome.index_price_ok),
            "staleness_param_ok": bool(outcome.staleness_param_ok),
            "oracle_fresh": bool(outcome.oracle_fresh),
            "clearing_price_ok": bool(outcome.clearing_price_ok),
            "max_oracle_move_ok": bool(outcome.max_oracle_move_ok),
            "funding_cap_ok": bool(outcome.funding_cap_ok),
            "net_funding_balanced": bool(outcome.net_funding_balanced),
            "funding_not_applied": bool(outcome.funding_not_applied),
            "funding_auto_allowed": bool(outcome.funding_auto_allowed),
        },
    )


def _commit_effect(adapter: PerpApplyFundingAutoGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[PerpApplyFundingAutoGateV1NativeAdapter, Any], Any]] = {
    "evaluate_apply_funding_auto_gate": _handle_evaluate_apply_funding_auto_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpApplyFundingAutoGateV1NativeAdapter, str, Any], None]] = {
    "clearing_price_seen_ok": _commit_effect,
    "clearing_price_epoch_ok": _commit_effect,
    "pre_settlement_window_ok": _commit_effect,
    "oracle_seen_ok": _commit_effect,
    "index_price_ok": _commit_effect,
    "staleness_param_ok": _commit_effect,
    "oracle_fresh": _commit_effect,
    "clearing_price_ok": _commit_effect,
    "max_oracle_move_ok": _commit_effect,
    "funding_cap_ok": _commit_effect,
    "net_funding_balanced": _commit_effect,
    "funding_not_applied": _commit_effect,
    "funding_auto_allowed": _commit_effect,
}


def make_adapter(ir: Any) -> PerpApplyFundingAutoGateV1NativeAdapter:
    return PerpApplyFundingAutoGateV1NativeAdapter(ir=ir)
