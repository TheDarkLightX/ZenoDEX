from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from .perp_liquidation_envelope import perp_liquidation_envelope_ok_bps


MARKET_KIND_INVALID = 0
MARKET_KIND_CH2P = 1
MARKET_KIND_CH3P = 2

REJECT_OK = "Ok"
REJECT_INVALID_MARKET_KIND = "InvalidMarketKind"
REJECT_OPERATOR_ONLY = "OperatorOnly"
REJECT_MID_EPOCH = "MidEpoch"
REJECT_PENALTY_INCREASE_WHILE_OPEN = "PenaltyIncreaseWhileOpen"
REJECT_PENALTY_ABOVE_MAINTENANCE = "PenaltyAboveMaintenance"
REJECT_UNFUNDED_LIQUIDATION_PENALTY = "UnfundedLiquidationPenalty"


@dataclass(frozen=True)
class PerpClearinghouseMarketParamsGuardOutcome:
    market_kind: int
    market_kind_ok: bool
    operator_ok: bool
    epoch_settled_ok: bool
    positions_open: bool
    penalty_increase_ok: bool
    penalty_below_maintenance_ok: bool
    funded_liquidation_ok: bool
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
    new_initial_margin_bps: Any,
    new_maintenance_margin_bps: Any,
    new_max_oracle_move_bps: Any,
) -> PerpClearinghouseMarketParamsGuardOutcome:
    kind = _require_market_kind(market_kind)
    operator = _require_flag(operator_ok, name="operator_ok")
    epoch_settled = _require_flag(epoch_settled_ok, name="epoch_settled_ok")
    pos_a = _require_int(position_base_a, name="position_base_a")
    pos_b = _require_int(position_base_b, name="position_base_b")
    pos_c = _require_int(position_base_c, name="position_base_c")
    old_penalty = _require_int(old_liquidation_penalty_bps, name="old_liquidation_penalty_bps")
    new_penalty = _require_int(new_liquidation_penalty_bps, name="new_liquidation_penalty_bps")
    new_initial = _require_int(new_initial_margin_bps, name="new_initial_margin_bps")
    new_maintenance = _require_int(new_maintenance_margin_bps, name="new_maintenance_margin_bps")
    new_max_move = _require_int(new_max_oracle_move_bps, name="new_max_oracle_move_bps")

    market_kind_ok = bool(kind in (MARKET_KIND_CH2P, MARKET_KIND_CH3P))
    if kind == MARKET_KIND_CH2P:
        positions_open = bool(pos_a != 0 or pos_b != 0)
    elif kind == MARKET_KIND_CH3P:
        positions_open = bool(pos_a != 0 or pos_b != 0 or pos_c != 0)
    else:
        positions_open = False

    penalty_increase_ok = bool((not positions_open) or new_penalty <= old_penalty)
    penalty_below_maintenance_ok = bool(new_penalty < new_maintenance)
    funded_liquidation_ok = perp_liquidation_envelope_ok_bps(
        initial_margin_bps=new_initial,
        maintenance_margin_bps=new_maintenance,
        depeg_buffer_bps=0,
        max_oracle_move_bps=new_max_move,
        liquidation_penalty_bps=new_penalty,
    )

    if not market_kind_ok:
        reject_code = REJECT_INVALID_MARKET_KIND
    elif not operator:
        reject_code = REJECT_OPERATOR_ONLY
    elif not epoch_settled:
        reject_code = REJECT_MID_EPOCH
    elif not penalty_increase_ok:
        reject_code = REJECT_PENALTY_INCREASE_WHILE_OPEN
    elif not penalty_below_maintenance_ok:
        reject_code = REJECT_PENALTY_ABOVE_MAINTENANCE
    elif not funded_liquidation_ok:
        reject_code = REJECT_UNFUNDED_LIQUIDATION_PENALTY
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
        funded_liquidation_ok=funded_liquidation_ok,
        admission_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks={
            "market_kind": kind,
            "operator_ok": operator,
            "epoch_settled_ok": epoch_settled,
            "positions_open": positions_open,
            "penalty_increase_ok": penalty_increase_ok,
            "penalty_below_maintenance_ok": penalty_below_maintenance_ok,
            "funded_liquidation_ok": funded_liquidation_ok,
            "new_initial_margin_bps": new_initial,
            "new_maintenance_margin_bps": new_maintenance,
            "new_max_oracle_move_bps": new_max_move,
            "new_liquidation_penalty_bps": new_penalty,
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
    if outcome.reject_code == REJECT_PENALTY_ABOVE_MAINTENANCE:
        return "invalid params: require liquidation_penalty_bps < maintenance_margin_bps"
    if outcome.reject_code == REJECT_UNFUNDED_LIQUIDATION_PENALTY:
        return (
            "invalid params: require funded liquidation "
            "liquidation_penalty_bps * (10000 + max_oracle_move_bps) <= "
            "10000 * (maintenance_margin_bps - max_oracle_move_bps)"
        )
    return None
