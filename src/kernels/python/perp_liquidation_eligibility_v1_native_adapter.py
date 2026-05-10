from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.perp_liquidation_eligibility_gate import evaluate_perp_liquidation_eligibility_gate

IR_HASH = "sha256:ef5b52acaf7e8dcd4e69c4245cc6894fe7c9df0f56d642d297aab16a6e087ad9"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class PerpLiquidationEligibilityV1NativeAdapter:
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


def _handle_evaluate_liquidation_eligibility(
    adapter: PerpLiquidationEligibilityV1NativeAdapter,
    command: Any,
) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_liquidation_eligibility"
    try:
        outcome = evaluate_perp_liquidation_eligibility_gate(
            now_epoch=s["now_epoch"],
            epoch_phase=s["epoch_phase"],
            auth_ok=s["auth_ok"],
            position_base=s["position_base"],
            index_price_e8=s["index_price_e8"],
            oracle_last_update_epoch=s["oracle_last_update_epoch"],
            max_oracle_staleness_epochs=s["max_oracle_staleness_epochs"],
            oracle_seen=s["oracle_seen"],
            collateral_quote=s["collateral_quote"],
            maintenance_margin_bps=s["maintenance_margin_bps"],
            depeg_buffer_bps=s["depeg_buffer_bps"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "phase_open_ok": bool(outcome.phase_open_ok),
            "auth_ok": bool(outcome.auth_ok),
            "position_open_ok": bool(outcome.position_open_ok),
            "index_price_ok": bool(outcome.index_price_ok),
            "staleness_param_ok": bool(outcome.staleness_param_ok),
            "oracle_seen_ok": bool(outcome.oracle_seen_ok),
            "oracle_fresh": bool(outcome.oracle_fresh),
            "effective_maint_bps": int(outcome.effective_maint_bps),
            "maint_req_quote": int(outcome.maint_req_quote),
            "liquidatable": bool(outcome.liquidatable),
            "partial_liquidation_allowed": bool(outcome.partial_liquidation_allowed),
        },
    )


def _commit_effect(adapter: PerpLiquidationEligibilityV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[PerpLiquidationEligibilityV1NativeAdapter, Any], Any]] = {
    "evaluate_liquidation_eligibility": _handle_evaluate_liquidation_eligibility,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpLiquidationEligibilityV1NativeAdapter, str, Any], None]] = {
    "phase_open_ok": _commit_effect,
    "auth_ok": _commit_effect,
    "position_open_ok": _commit_effect,
    "index_price_ok": _commit_effect,
    "staleness_param_ok": _commit_effect,
    "oracle_seen_ok": _commit_effect,
    "oracle_fresh": _commit_effect,
    "effective_maint_bps": _commit_effect,
    "maint_req_quote": _commit_effect,
    "liquidatable": _commit_effect,
    "partial_liquidation_allowed": _commit_effect,
}


def make_adapter(ir: Any) -> PerpLiquidationEligibilityV1NativeAdapter:
    return PerpLiquidationEligibilityV1NativeAdapter(ir=ir)
