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
ACTION_PARTIAL_LIQUIDATE = 10
ACTION_CARRY_FUNDING_CLOSEOUT_LIABILITY = 11
ACTION_SETTLE_FUNDING_CLOSEOUT_CARRIED_LIABILITY = 12
ACTION_SETTLE_FUNDING_CLOSEOUT_RECOVERY = 13

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
        ACTION_CARRY_FUNDING_CLOSEOUT_LIABILITY,
        ACTION_SETTLE_FUNDING_CLOSEOUT_CARRIED_LIABILITY,
        ACTION_SETTLE_FUNDING_CLOSEOUT_RECOVERY,
    }
)
_SENDER_BOUND_ACTIONS = frozenset(
    {
        ACTION_DEPOSIT_COLLATERAL,
        ACTION_WITHDRAW_COLLATERAL,
        ACTION_SET_POSITION,
        ACTION_PARTIAL_LIQUIDATE,
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


@dataclass(frozen=True)
class _RuntimeRiskFlags:
    operator_ok: bool
    unknown_fields_ok: bool
    sender_binding_ok: bool
    epoch_settled_ok: bool
    positive_price_ok: bool
    positions_flat_ok: bool
    params_object_ok: bool


@dataclass(frozen=True)
class _RuntimeRiskRequirements:
    action_known: bool
    operator_required: bool
    sender_binding_required: bool
    epoch_settled_required: bool
    positive_price_required: bool
    positions_flat_required: bool
    params_object_required: bool


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
    if value < ACTION_INVALID or value > ACTION_SETTLE_FUNDING_CLOSEOUT_RECOVERY:
        raise ValueError(f"{name} out of range")
    return int(value)


def _runtime_risk_requirements(action: int) -> _RuntimeRiskRequirements:
    return _RuntimeRiskRequirements(
        action_known=bool(action != ACTION_INVALID),
        operator_required=bool(action in _OPERATOR_ACTIONS),
        sender_binding_required=bool(action in _SENDER_BOUND_ACTIONS),
        epoch_settled_required=bool(action in (ACTION_ADVANCE_EPOCH, ACTION_SET_MARKET_PARAMS)),
        positive_price_required=bool(action == ACTION_PUBLISH_CLEARING_PRICE),
        positions_flat_required=bool(action == ACTION_CLEAR_BREAKER),
        params_object_required=bool(action == ACTION_SET_MARKET_PARAMS),
    )


def _runtime_risk_checks(action: int, flags: _RuntimeRiskFlags) -> Mapping[str, bool | int]:
    return {
        "action_kind": action,
        "operator_ok": flags.operator_ok,
        "unknown_fields_ok": flags.unknown_fields_ok,
        "sender_binding_ok": flags.sender_binding_ok,
        "epoch_settled_ok": flags.epoch_settled_ok,
        "positive_price_ok": flags.positive_price_ok,
        "positions_flat_ok": flags.positions_flat_ok,
        "params_object_ok": flags.params_object_ok,
    }


def _runtime_risk_reject_code(
    action: int,
    *,
    flags: _RuntimeRiskFlags,
    requirements: _RuntimeRiskRequirements,
) -> str:
    if not requirements.action_known:
        return REJECT_INVALID_ACTION
    if requirements.operator_required and not flags.operator_ok:
        return REJECT_OPERATOR_ONLY
    if not flags.unknown_fields_ok:
        return REJECT_UNKNOWN_FIELDS
    if requirements.sender_binding_required and not flags.sender_binding_ok:
        return REJECT_SENDER_BINDING_INVALID
    if action == ACTION_ADVANCE_EPOCH and not flags.epoch_settled_ok:
        return REJECT_EPOCH_NOT_SETTLED
    if action == ACTION_PUBLISH_CLEARING_PRICE and not flags.positive_price_ok:
        return REJECT_PRICE_INVALID
    if action == ACTION_CLEAR_BREAKER and not flags.positions_flat_ok:
        return REJECT_POSITIONS_OPEN
    if action == ACTION_SET_MARKET_PARAMS and not flags.epoch_settled_ok:
        return REJECT_MARKET_PARAMS_MID_EPOCH
    if action == ACTION_SET_MARKET_PARAMS and not flags.params_object_ok:
        return REJECT_PARAMS_OBJECT_INVALID
    return REJECT_OK


def _runtime_risk_outcome(
    action: int,
    *,
    flags: _RuntimeRiskFlags,
    requirements: _RuntimeRiskRequirements,
    reject_code: str,
) -> PerpRuntimeRiskGateOutcome:
    return PerpRuntimeRiskGateOutcome(
        action_kind=action,
        action_known=requirements.action_known,
        operator_required=requirements.operator_required,
        operator_ok=flags.operator_ok,
        unknown_fields_ok=flags.unknown_fields_ok,
        sender_binding_required=requirements.sender_binding_required,
        sender_binding_ok=flags.sender_binding_ok,
        epoch_settled_required=requirements.epoch_settled_required,
        epoch_settled_ok=flags.epoch_settled_ok,
        positive_price_required=requirements.positive_price_required,
        positive_price_ok=flags.positive_price_ok,
        positions_flat_required=requirements.positions_flat_required,
        positions_flat_ok=flags.positions_flat_ok,
        params_object_required=requirements.params_object_required,
        params_object_ok=flags.params_object_ok,
        admission_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks=_runtime_risk_checks(action, flags),
    )


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
    flags = _RuntimeRiskFlags(
        operator_ok=_require_flag(operator_ok, name="operator_ok"),
        unknown_fields_ok=_require_flag(unknown_fields_ok, name="unknown_fields_ok"),
        sender_binding_ok=_require_flag(sender_binding_ok, name="sender_binding_ok"),
        epoch_settled_ok=_require_flag(epoch_settled_ok, name="epoch_settled_ok"),
        positive_price_ok=_require_flag(positive_price_ok, name="positive_price_ok"),
        positions_flat_ok=_require_flag(positions_flat_ok, name="positions_flat_ok"),
        params_object_ok=_require_flag(params_object_ok, name="params_object_ok"),
    )
    requirements = _runtime_risk_requirements(action)
    reject_code = _runtime_risk_reject_code(action, flags=flags, requirements=requirements)
    return _runtime_risk_outcome(action, flags=flags, requirements=requirements, reject_code=reject_code)


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
