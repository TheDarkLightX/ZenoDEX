from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping


MARKET_KIND_INVALID = 0
MARKET_KIND_CH2P = 1
MARKET_KIND_CH3P = 2

REJECT_OK = "Ok"
REJECT_INVALID_MARKET_KIND = "InvalidMarketKind"
REJECT_OPERATOR_ONLY = "OperatorOnly"
REJECT_MID_EPOCH = "MidEpoch"
REJECT_PENALTY_INCREASE_WHILE_OPEN = "PenaltyIncreaseWhileOpen"
REJECT_PENALTY_ABOVE_MAINTENANCE = "PenaltyAboveMaintenance"
REJECT_MAX_ORACLE_MOVE_INCREASE_WHILE_OPEN = "MaxOracleMoveIncreaseWhileOpen"
REJECT_MAX_ORACLE_STALENESS_INCREASE_WHILE_OPEN = "MaxOracleStalenessIncreaseWhileOpen"
REJECT_INITIAL_MARGIN_DECREASE_WHILE_OPEN = "InitialMarginDecreaseWhileOpen"
REJECT_MAINTENANCE_MARGIN_DECREASE_WHILE_OPEN = "MaintenanceMarginDecreaseWhileOpen"
REJECT_MAX_POSITION_INCREASE_WHILE_OPEN = "MaxPositionIncreaseWhileOpen"


@dataclass(frozen=True)
class PerpClearinghouseMarketParamsGuardOutcome:
    market_kind: int
    market_kind_ok: bool
    operator_ok: bool
    epoch_settled_ok: bool
    positions_open: bool
    penalty_increase_ok: bool
    penalty_below_maintenance_ok: bool
    max_oracle_move_increase_ok: bool
    max_oracle_staleness_increase_ok: bool
    initial_margin_decrease_ok: bool
    maintenance_margin_decrease_ok: bool
    max_position_increase_ok: bool
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


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_market_kind(value: Any, *, name: str = "market_kind") -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < MARKET_KIND_INVALID or value > MARKET_KIND_CH3P:
        raise ValueError(f"{name} out of range")
    return int(value)


def evaluate_perp_clearinghouse_market_params_guard(
    *,
    market_kind: Any,
    operator_ok: Any,
    epoch_settled_ok: Any,
    position_base_a: Any,
    position_base_b: Any,
    position_base_c: Any,
    old_liquidation_penalty_bps: Any,
    new_liquidation_penalty_bps: Any,
    old_max_oracle_move_bps: Any,
    new_max_oracle_move_bps: Any,
    old_max_oracle_staleness_epochs: Any,
    new_max_oracle_staleness_epochs: Any,
    old_initial_margin_bps: Any,
    new_initial_margin_bps: Any,
    old_maintenance_margin_bps: Any,
    new_maintenance_margin_bps: Any,
    old_max_position_abs: Any,
    new_max_position_abs: Any,
) -> PerpClearinghouseMarketParamsGuardOutcome:
    kind = _require_market_kind(market_kind)
    operator = _require_flag(operator_ok, name="operator_ok")
    epoch_settled = _require_flag(epoch_settled_ok, name="epoch_settled_ok")
    pos_a = _require_int(position_base_a, name="position_base_a")
    pos_b = _require_int(position_base_b, name="position_base_b")
    pos_c = _require_int(position_base_c, name="position_base_c")
    old_penalty = _require_int(old_liquidation_penalty_bps, name="old_liquidation_penalty_bps")
    new_penalty = _require_int(new_liquidation_penalty_bps, name="new_liquidation_penalty_bps")
    old_max_move = _require_int(old_max_oracle_move_bps, name="old_max_oracle_move_bps")
    new_max_move = _require_int(new_max_oracle_move_bps, name="new_max_oracle_move_bps")
    old_max_staleness = _require_int(old_max_oracle_staleness_epochs, name="old_max_oracle_staleness_epochs")
    new_max_staleness = _require_int(new_max_oracle_staleness_epochs, name="new_max_oracle_staleness_epochs")
    old_initial = _require_int(old_initial_margin_bps, name="old_initial_margin_bps")
    new_initial = _require_int(new_initial_margin_bps, name="new_initial_margin_bps")
    old_maintenance = _require_int(old_maintenance_margin_bps, name="old_maintenance_margin_bps")
    new_maintenance = _require_int(new_maintenance_margin_bps, name="new_maintenance_margin_bps")
    old_max_position = _require_int(old_max_position_abs, name="old_max_position_abs")
    new_max_position = _require_int(new_max_position_abs, name="new_max_position_abs")

    market_kind_ok = bool(kind in (MARKET_KIND_CH2P, MARKET_KIND_CH3P))
    if kind == MARKET_KIND_CH2P:
        positions_open = bool(pos_a != 0 or pos_b != 0)
    elif kind == MARKET_KIND_CH3P:
        positions_open = bool(pos_a != 0 or pos_b != 0 or pos_c != 0)
    else:
        positions_open = False

    penalty_increase_ok = bool((not positions_open) or new_penalty <= old_penalty)
    penalty_below_maintenance_ok = bool(new_penalty < new_maintenance)
    max_oracle_move_increase_ok = bool((not positions_open) or new_max_move <= old_max_move)
    max_oracle_staleness_increase_ok = bool((not positions_open) or new_max_staleness <= old_max_staleness)
    initial_margin_decrease_ok = bool((not positions_open) or new_initial >= old_initial)
    maintenance_margin_decrease_ok = bool((not positions_open) or new_maintenance >= old_maintenance)
    max_position_increase_ok = bool((not positions_open) or new_max_position <= old_max_position)

    if not market_kind_ok:
        reject_code = REJECT_INVALID_MARKET_KIND
    elif not operator:
        reject_code = REJECT_OPERATOR_ONLY
    elif not epoch_settled:
        reject_code = REJECT_MID_EPOCH
    elif not penalty_increase_ok:
        reject_code = REJECT_PENALTY_INCREASE_WHILE_OPEN
    elif not max_oracle_move_increase_ok:
        reject_code = REJECT_MAX_ORACLE_MOVE_INCREASE_WHILE_OPEN
    elif not max_oracle_staleness_increase_ok:
        reject_code = REJECT_MAX_ORACLE_STALENESS_INCREASE_WHILE_OPEN
    elif not initial_margin_decrease_ok:
        reject_code = REJECT_INITIAL_MARGIN_DECREASE_WHILE_OPEN
    elif not maintenance_margin_decrease_ok:
        reject_code = REJECT_MAINTENANCE_MARGIN_DECREASE_WHILE_OPEN
    elif not max_position_increase_ok:
        reject_code = REJECT_MAX_POSITION_INCREASE_WHILE_OPEN
    elif not penalty_below_maintenance_ok:
        reject_code = REJECT_PENALTY_ABOVE_MAINTENANCE
    else:
        reject_code = REJECT_OK

    return PerpClearinghouseMarketParamsGuardOutcome(
        market_kind=kind,
        market_kind_ok=market_kind_ok,
        operator_ok=operator,
        epoch_settled_ok=epoch_settled,
        positions_open=positions_open,
        penalty_increase_ok=penalty_increase_ok,
        penalty_below_maintenance_ok=penalty_below_maintenance_ok,
        max_oracle_move_increase_ok=max_oracle_move_increase_ok,
        max_oracle_staleness_increase_ok=max_oracle_staleness_increase_ok,
        initial_margin_decrease_ok=initial_margin_decrease_ok,
        maintenance_margin_decrease_ok=maintenance_margin_decrease_ok,
        max_position_increase_ok=max_position_increase_ok,
        admission_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks={
            "market_kind": kind,
            "operator_ok": operator,
            "epoch_settled_ok": epoch_settled,
            "positions_open": positions_open,
            "penalty_increase_ok": penalty_increase_ok,
            "penalty_below_maintenance_ok": penalty_below_maintenance_ok,
            "max_oracle_move_increase_ok": max_oracle_move_increase_ok,
            "max_oracle_staleness_increase_ok": max_oracle_staleness_increase_ok,
            "initial_margin_decrease_ok": initial_margin_decrease_ok,
            "maintenance_margin_decrease_ok": maintenance_margin_decrease_ok,
            "max_position_increase_ok": max_position_increase_ok,
        },
    )


def perp_clearinghouse_market_params_guard_error(
    outcome: PerpClearinghouseMarketParamsGuardOutcome,
) -> str | None:
    if outcome.reject_code == REJECT_INVALID_MARKET_KIND:
        return "invalid clearinghouse market kind"
    if outcome.reject_code == REJECT_OPERATOR_ONLY:
        return "operator only"
    if outcome.reject_code == REJECT_MID_EPOCH:
        return "cannot update market params mid-epoch"
    if outcome.reject_code == REJECT_PENALTY_INCREASE_WHILE_OPEN:
        return "invalid params: cannot increase liquidation_penalty_bps while positions are open"
    if outcome.reject_code == REJECT_MAX_ORACLE_MOVE_INCREASE_WHILE_OPEN:
        return "invalid params: cannot increase max_oracle_move_bps while positions are open"
    if outcome.reject_code == REJECT_MAX_ORACLE_STALENESS_INCREASE_WHILE_OPEN:
        return "invalid params: cannot increase max_oracle_staleness_epochs while positions are open"
    if outcome.reject_code == REJECT_INITIAL_MARGIN_DECREASE_WHILE_OPEN:
        return "invalid params: cannot decrease initial_margin_bps while positions are open"
    if outcome.reject_code == REJECT_MAINTENANCE_MARGIN_DECREASE_WHILE_OPEN:
        return "invalid params: cannot decrease maintenance_margin_bps while positions are open"
    if outcome.reject_code == REJECT_MAX_POSITION_INCREASE_WHILE_OPEN:
        return "invalid params: cannot increase max_position_abs while positions are open"
    if outcome.reject_code == REJECT_PENALTY_ABOVE_MAINTENANCE:
        return "invalid params: require liquidation_penalty_bps < maintenance_margin_bps"
    return None
