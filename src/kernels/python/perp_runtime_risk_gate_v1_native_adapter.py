from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.perp_runtime_risk_gate import evaluate_perp_runtime_risk_gate

IR_HASH = "sha256:dca130b2c88064492fab7e8dbfd863e2402a3aa1855849eaf25a01325a2620b6"

_REJECT_CODE_TO_INT = {
    "Ok": 0,
    "InvalidAction": 1,
    "OperatorOnly": 2,
    "UnknownFields": 3,
    "EpochNotSettled": 4,
    "PriceInvalid": 5,
    "PositionsOpen": 6,
    "MarketParamsMidEpoch": 7,
    "ParamsObjectInvalid": 8,
    "SenderBindingInvalid": 9,
}


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class PerpRuntimeRiskGateV1NativeAdapter:
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


def _handle_evaluate_runtime_risk_gate(adapter: PerpRuntimeRiskGateV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_runtime_risk_gate"
    try:
        outcome = evaluate_perp_runtime_risk_gate(
            action_kind=s["action_kind"],
            operator_ok=s["operator_ok"],
            unknown_fields_ok=s["unknown_fields_ok"],
            sender_binding_ok=s["sender_binding_ok"],
            epoch_settled_ok=s["epoch_settled_ok"],
            positive_price_ok=s["positive_price_ok"],
            positions_flat_ok=s["positions_flat_ok"],
            params_object_ok=s["params_object_ok"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "action_known": bool(outcome.action_known),
            "operator_required": bool(outcome.operator_required),
            "operator_ok": bool(outcome.operator_ok),
            "unknown_fields_ok": bool(outcome.unknown_fields_ok),
            "sender_binding_required": bool(outcome.sender_binding_required),
            "sender_binding_ok": bool(outcome.sender_binding_ok),
            "epoch_settled_required": bool(outcome.epoch_settled_required),
            "epoch_settled_ok": bool(outcome.epoch_settled_ok),
            "positive_price_required": bool(outcome.positive_price_required),
            "positive_price_ok": bool(outcome.positive_price_ok),
            "positions_flat_required": bool(outcome.positions_flat_required),
            "positions_flat_ok": bool(outcome.positions_flat_ok),
            "params_object_required": bool(outcome.params_object_required),
            "params_object_ok": bool(outcome.params_object_ok),
            "admission_ok": bool(outcome.admission_ok),
            "reject_code": int(_REJECT_CODE_TO_INT[outcome.reject_code]),
        },
    )


def _commit_effect(adapter: PerpRuntimeRiskGateV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[PerpRuntimeRiskGateV1NativeAdapter, Any], Any]] = {
    "evaluate_runtime_risk_gate": _handle_evaluate_runtime_risk_gate,
}

EFFECT_HANDLERS: dict[str, Callable[[PerpRuntimeRiskGateV1NativeAdapter, str, Any], None]] = {
    "action_known": _commit_effect,
    "operator_required": _commit_effect,
    "operator_ok": _commit_effect,
    "unknown_fields_ok": _commit_effect,
    "sender_binding_required": _commit_effect,
    "sender_binding_ok": _commit_effect,
    "epoch_settled_required": _commit_effect,
    "epoch_settled_ok": _commit_effect,
    "positive_price_required": _commit_effect,
    "positive_price_ok": _commit_effect,
    "positions_flat_required": _commit_effect,
    "positions_flat_ok": _commit_effect,
    "params_object_required": _commit_effect,
    "params_object_ok": _commit_effect,
    "admission_ok": _commit_effect,
    "reject_code": _commit_effect,
}


def make_adapter(ir: Any) -> PerpRuntimeRiskGateV1NativeAdapter:
    return PerpRuntimeRiskGateV1NativeAdapter(ir=ir)
