from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping


ACTION_INVALID = 0
ACTION_ADVANCE_EPOCH = 1
ACTION_PUBLISH_CLEARING_PRICE = 2
ACTION_APPLY_FUNDING_AUTO = 3
ACTION_SETTLE_EPOCH = 4
ACTION_CLEAR_BREAKER = 5
ACTION_SET_MARKET_PARAMS = 6
ACTION_DEPOSIT_COLLATERAL = 7
ACTION_WITHDRAW_COLLATERAL = 8
ACTION_SET_POSITION = 9

REJECT_OK = "Ok"
REJECT_INVALID_ACTION = "InvalidAction"
REJECT_OPERATOR_ONLY = "OperatorOnly"
REJECT_UNKNOWN_FIELDS = "UnknownFields"
REJECT_EPOCH_NOT_SETTLED = "EpochNotSettled"
REJECT_PRICE_INVALID = "PriceInvalid"
REJECT_POSITIONS_OPEN = "PositionsOpen"
REJECT_MARKET_PARAMS_MID_EPOCH = "MarketParamsMidEpoch"
REJECT_PARAMS_OBJECT_INVALID = "ParamsObjectInvalid"
REJECT_SENDER_BINDING_INVALID = "SenderBindingInvalid"

_OPERATOR_ACTIONS = frozenset(
    {
        ACTION_ADVANCE_EPOCH,
        ACTION_PUBLISH_CLEARING_PRICE,
        ACTION_APPLY_FUNDING_AUTO,
        ACTION_SETTLE_EPOCH,
        ACTION_CLEAR_BREAKER,
        ACTION_SET_MARKET_PARAMS,
    }
)
_SENDER_BOUND_ACTIONS = frozenset(
    {
        ACTION_DEPOSIT_COLLATERAL,
        ACTION_WITHDRAW_COLLATERAL,
        ACTION_SET_POSITION,
    }
)


@dataclass(frozen=True)
class PerpRuntimeRiskGateOutcome:
    action_kind: int
    action_known: bool
    operator_required: bool
    operator_ok: bool
    unknown_fields_ok: bool
    sender_binding_required: bool
    sender_binding_ok: bool
    epoch_settled_required: bool
    epoch_settled_ok: bool
    positive_price_required: bool
    positive_price_ok: bool
    positions_flat_required: bool
    positions_flat_ok: bool
    params_object_required: bool
    params_object_ok: bool
    admission_ok: bool
    reject_code: str
    checks: Mapping[str, bool | int]


def _require_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return bool(value)
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be a bool or 0/1 int")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return bool(value)


def _require_action_kind(value: Any, *, name: str = "action_kind") -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < ACTION_INVALID or value > ACTION_SET_POSITION:
        raise ValueError(f"{name} out of range")
    return int(value)


def evaluate_perp_runtime_risk_gate(
    *,
    action_kind: Any,
    operator_ok: Any,
    unknown_fields_ok: Any,
    sender_binding_ok: Any,
    epoch_settled_ok: Any,
    positive_price_ok: Any,
    positions_flat_ok: Any,
    params_object_ok: Any,
) -> PerpRuntimeRiskGateOutcome:
    action = _require_action_kind(action_kind)
    operator = _require_flag(operator_ok, name="operator_ok")
    unknown_fields = _require_flag(unknown_fields_ok, name="unknown_fields_ok")
    sender_binding = _require_flag(sender_binding_ok, name="sender_binding_ok")
    epoch_settled = _require_flag(epoch_settled_ok, name="epoch_settled_ok")
    positive_price = _require_flag(positive_price_ok, name="positive_price_ok")
    positions_flat = _require_flag(positions_flat_ok, name="positions_flat_ok")
    params_object = _require_flag(params_object_ok, name="params_object_ok")

    action_known = bool(action != ACTION_INVALID)
    operator_required = bool(action in _OPERATOR_ACTIONS)
    sender_binding_required = bool(action in _SENDER_BOUND_ACTIONS)
    epoch_settled_required = bool(action in (ACTION_ADVANCE_EPOCH, ACTION_SET_MARKET_PARAMS))
    positive_price_required = bool(action == ACTION_PUBLISH_CLEARING_PRICE)
    positions_flat_required = bool(action == ACTION_CLEAR_BREAKER)
    params_object_required = bool(action == ACTION_SET_MARKET_PARAMS)

    checks = {
        "action_kind": action,
        "operator_ok": operator,
        "unknown_fields_ok": unknown_fields,
        "sender_binding_ok": sender_binding,
        "epoch_settled_ok": epoch_settled,
        "positive_price_ok": positive_price,
        "positions_flat_ok": positions_flat,
        "params_object_ok": params_object,
    }

    if not action_known:
        reject_code = REJECT_INVALID_ACTION
    elif operator_required and not operator:
        reject_code = REJECT_OPERATOR_ONLY
    elif not unknown_fields:
        reject_code = REJECT_UNKNOWN_FIELDS
    elif sender_binding_required and not sender_binding:
        reject_code = REJECT_SENDER_BINDING_INVALID
    elif action == ACTION_ADVANCE_EPOCH and not epoch_settled:
        reject_code = REJECT_EPOCH_NOT_SETTLED
    elif action == ACTION_PUBLISH_CLEARING_PRICE and not positive_price:
        reject_code = REJECT_PRICE_INVALID
    elif action == ACTION_CLEAR_BREAKER and not positions_flat:
        reject_code = REJECT_POSITIONS_OPEN
    elif action == ACTION_SET_MARKET_PARAMS and not epoch_settled:
        reject_code = REJECT_MARKET_PARAMS_MID_EPOCH
    elif action == ACTION_SET_MARKET_PARAMS and not params_object:
        reject_code = REJECT_PARAMS_OBJECT_INVALID
    else:
        reject_code = REJECT_OK

    return PerpRuntimeRiskGateOutcome(
        action_kind=action,
        action_known=action_known,
        operator_required=operator_required,
        operator_ok=operator,
        unknown_fields_ok=unknown_fields,
        sender_binding_required=sender_binding_required,
        sender_binding_ok=sender_binding,
        epoch_settled_required=epoch_settled_required,
        epoch_settled_ok=epoch_settled,
        positive_price_required=positive_price_required,
        positive_price_ok=positive_price,
        positions_flat_required=positions_flat_required,
        positions_flat_ok=positions_flat,
        params_object_required=params_object_required,
        params_object_ok=params_object,
        admission_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks=checks,
    )


def perp_runtime_risk_gate_error(outcome: PerpRuntimeRiskGateOutcome, *, action: str) -> str | None:
    if outcome.reject_code == REJECT_INVALID_ACTION:
        return f"unknown perps action: {action}"
    if outcome.reject_code == REJECT_OPERATOR_ONLY:
        return "operator only"
    if outcome.reject_code == REJECT_UNKNOWN_FIELDS:
        return f"{action} has unknown fields"
    if outcome.reject_code == REJECT_EPOCH_NOT_SETTLED:
        return "cannot advance epoch before settling current epoch"
    if outcome.reject_code == REJECT_PRICE_INVALID:
        return "publish_clearing_price requires price_e8 > 0"
    if outcome.reject_code == REJECT_POSITIONS_OPEN:
        return "cannot clear breaker while positions are open"
    if outcome.reject_code == REJECT_MARKET_PARAMS_MID_EPOCH:
        return "cannot update market params mid-epoch"
    if outcome.reject_code == REJECT_PARAMS_OBJECT_INVALID:
        return "params must be an object"
    if outcome.reject_code == REJECT_SENDER_BINDING_INVALID:
        return "account_pubkey must match tx sender"
    return None
