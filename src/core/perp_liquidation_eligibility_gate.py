from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .perp_v2.math import is_liquidatable, is_oracle_fresh, maint_margin_req
from .perp_v2.types import EpochPhase

_PHASE_TO_INT = {
    EpochPhase.OPEN: 0,
    EpochPhase.PRICE_PUBLISHED: 1,
    EpochPhase.SETTLED: 2,
}


@dataclass(frozen=True)
class PerpLiquidationEligibilityOutcome:
    phase_open_ok: bool
    auth_ok: bool
    position_open_ok: bool
    index_price_ok: bool
    staleness_param_ok: bool
    oracle_seen_ok: bool
    oracle_fresh: bool
    effective_maint_bps: int
    maint_req_quote: int
    liquidatable: bool
    partial_liquidation_allowed: bool


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return bool(value)
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be a bool or 0/1 int")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return bool(value)


def _require_epoch_phase(value: Any, *, name: str) -> int:
    if isinstance(value, EpochPhase):
        return _PHASE_TO_INT[value]
    phase = _require_int(value, name=name)
    if phase < 0 or phase > 2:
        raise ValueError(f"{name} must be in [0, 2]")
    return phase


def evaluate_perp_liquidation_eligibility_gate(
    *,
    now_epoch: int,
    epoch_phase: Any,
    auth_ok: Any,
    position_base: int,
    index_price_e8: int,
    oracle_last_update_epoch: int,
    max_oracle_staleness_epochs: int,
    oracle_seen: Any,
    collateral_quote: int,
    maintenance_margin_bps: int,
    depeg_buffer_bps: int,
) -> PerpLiquidationEligibilityOutcome:
    now = _require_int(now_epoch, name="now_epoch")
    phase = _require_epoch_phase(epoch_phase, name="epoch_phase")
    auth = _require_flag(auth_ok, name="auth_ok")
    position = _require_int(position_base, name="position_base")
    index_price = _require_int(index_price_e8, name="index_price_e8")
    oracle_last = _require_int(oracle_last_update_epoch, name="oracle_last_update_epoch")
    max_staleness = _require_int(max_oracle_staleness_epochs, name="max_oracle_staleness_epochs")
    oracle_seen_flag = _require_flag(oracle_seen, name="oracle_seen")
    collateral = _require_int(collateral_quote, name="collateral_quote")
    maintenance_bps = _require_int(maintenance_margin_bps, name="maintenance_margin_bps")
    depeg_bps = _require_int(depeg_buffer_bps, name="depeg_buffer_bps")

    phase_open_ok = phase == _PHASE_TO_INT[EpochPhase.OPEN]
    position_open_ok = position != 0
    index_price_ok = index_price > 0
    staleness_param_ok = max_staleness > 0
    oracle_seen_ok = oracle_seen_flag
    oracle_fresh = is_oracle_fresh(now, oracle_last, max_staleness, oracle_seen_flag)
    effective_maint_bps = maintenance_bps + depeg_bps
    maint_req_quote = 0
    if position_open_ok and index_price_ok:
        maint_req_quote = maint_margin_req(position, index_price, maintenance_bps, depeg_bps)
    liquidatable = bool(
        position_open_ok
        and index_price_ok
        and is_liquidatable(position, collateral, index_price, maintenance_bps, depeg_bps)
    )
    partial_liquidation_allowed = bool(
        phase_open_ok
        and auth
        and position_open_ok
        and index_price_ok
        and oracle_fresh
        and liquidatable
    )

    return PerpLiquidationEligibilityOutcome(
        phase_open_ok=phase_open_ok,
        auth_ok=auth,
        position_open_ok=position_open_ok,
        index_price_ok=index_price_ok,
        staleness_param_ok=staleness_param_ok,
        oracle_seen_ok=oracle_seen_ok,
        oracle_fresh=oracle_fresh,
        effective_maint_bps=effective_maint_bps,
        maint_req_quote=maint_req_quote,
        liquidatable=liquidatable,
        partial_liquidation_allowed=partial_liquidation_allowed,
    )


def perp_liquidation_eligibility_gate_error(
    outcome: PerpLiquidationEligibilityOutcome,
) -> str | None:
    if not outcome.phase_open_ok:
        return "partial_liquidate only allowed during open phase"
    if not outcome.auth_ok:
        return "partial_liquidate requires auth"
    if not outcome.position_open_ok:
        return "partial_liquidate requires non-zero position"
    if not outcome.index_price_ok:
        return "partial_liquidate requires positive index_price_e8"
    if not outcome.oracle_seen_ok:
        return "partial_liquidate requires oracle_seen"
    if not outcome.staleness_param_ok:
        return "partial_liquidate requires valid max_oracle_staleness_epochs"
    if not outcome.oracle_fresh:
        return "partial_liquidate requires fresh oracle"
    if not outcome.liquidatable:
        return "partial_liquidate requires liquidatable account"
    return None
