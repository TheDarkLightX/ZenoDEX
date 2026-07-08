"""Typed liquidation parameter envelope for perps market admission."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .perp_v2.math import BPS_SCALE


@dataclass(frozen=True)
class PerpLiquidationEnvelopeBps:
    initial_margin_bps: int
    maintenance_margin_bps: int
    depeg_buffer_bps: int
    max_oracle_move_bps: int
    liquidation_penalty_bps: int

    @property
    def effective_maintenance_bps(self) -> int:
        return self.maintenance_margin_bps + self.depeg_buffer_bps


def _require_bps(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if int(value) < 0 or int(value) > BPS_SCALE:
        raise ValueError(f"{name} must be in [0, {BPS_SCALE}]")
    return int(value)


def require_perp_liquidation_envelope_bps(
    *,
    initial_margin_bps: Any,
    maintenance_margin_bps: Any,
    depeg_buffer_bps: Any,
    max_oracle_move_bps: Any,
    liquidation_penalty_bps: Any,
) -> PerpLiquidationEnvelopeBps:
    """Build a funded liquidation envelope or reject the parameter state."""
    initial = _require_bps(initial_margin_bps, name="initial_margin_bps")
    maintenance = _require_bps(maintenance_margin_bps, name="maintenance_margin_bps")
    depeg = _require_bps(depeg_buffer_bps, name="depeg_buffer_bps")
    max_move = _require_bps(max_oracle_move_bps, name="max_oracle_move_bps")
    penalty = _require_bps(liquidation_penalty_bps, name="liquidation_penalty_bps")

    effective = maintenance + depeg
    if effective > BPS_SCALE:
        raise ValueError(f"maintenance_margin_bps + depeg_buffer_bps must be <= {BPS_SCALE}")
    if max_move >= effective:
        raise ValueError("max_oracle_move_bps must be < maintenance_margin_bps + depeg_buffer_bps")
    if effective > initial:
        raise ValueError("maintenance_margin_bps + depeg_buffer_bps must be <= initial_margin_bps")
    if penalty >= effective:
        raise ValueError("liquidation_penalty_bps must be < maintenance_margin_bps + depeg_buffer_bps")
    if penalty * (BPS_SCALE + max_move) > BPS_SCALE * (effective - max_move):
        raise ValueError(
            "liquidation_penalty_bps * (10000 + max_oracle_move_bps) must be <= "
            "10000 * (maintenance_margin_bps + depeg_buffer_bps - max_oracle_move_bps)"
        )
    return PerpLiquidationEnvelopeBps(
        initial_margin_bps=initial,
        maintenance_margin_bps=maintenance,
        depeg_buffer_bps=depeg,
        max_oracle_move_bps=max_move,
        liquidation_penalty_bps=penalty,
    )


def perp_liquidation_envelope_ok_bps(
    *,
    initial_margin_bps: Any,
    maintenance_margin_bps: Any,
    depeg_buffer_bps: Any,
    max_oracle_move_bps: Any,
    liquidation_penalty_bps: Any,
) -> bool:
    try:
        require_perp_liquidation_envelope_bps(
            initial_margin_bps=initial_margin_bps,
            maintenance_margin_bps=maintenance_margin_bps,
            depeg_buffer_bps=depeg_buffer_bps,
            max_oracle_move_bps=max_oracle_move_bps,
            liquidation_penalty_bps=liquidation_penalty_bps,
        )
    except (TypeError, ValueError):
        return False
    return True
