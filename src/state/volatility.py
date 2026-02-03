"""Volatility tier state for dynamic fee adjustment.

Maps bounded volatility observations to fee tiers (0-3) with:
- Fail-closed: invalid data → tier 3 (halt)
- Monotone within epoch: tier cannot decrease within same epoch
- De-escalation on epoch advance: tier resets to observed level

Tier semantics:
  0 = calm     → 1x fee, 100% trade cap
  1 = elevated → 2x fee, 100% trade cap
  2 = high     → 3x fee, 10% trade cap
  3 = halt     → no trading
"""

from __future__ import annotations

from dataclasses import dataclass, replace


BPS_DENOM = 10_000


@dataclass(frozen=True)
class TierState:
    """Immutable volatility tier state matching ESSO model state vars."""

    tier: int = 0
    last_epoch: int = 0
    t1_bps: int = 3000
    t2_bps: int = 6000
    t3_bps: int = 8000

    def __post_init__(self) -> None:
        for name, val in (
            ("tier", self.tier),
            ("last_epoch", self.last_epoch),
            ("t1_bps", self.t1_bps),
            ("t2_bps", self.t2_bps),
            ("t3_bps", self.t3_bps),
        ):
            if not isinstance(val, int) or isinstance(val, bool):
                raise TypeError(f"{name} must be an int")
        if not (0 <= self.tier <= 3):
            raise ValueError(f"tier must be in [0, 3]: {self.tier}")
        if self.last_epoch < 0:
            raise ValueError(f"last_epoch must be non-negative: {self.last_epoch}")
        if not (0 <= self.t1_bps <= BPS_DENOM):
            raise ValueError(f"t1_bps must be in [0, {BPS_DENOM}]: {self.t1_bps}")
        if not (0 <= self.t2_bps <= BPS_DENOM):
            raise ValueError(f"t2_bps must be in [0, {BPS_DENOM}]: {self.t2_bps}")
        if not (0 <= self.t3_bps <= BPS_DENOM):
            raise ValueError(f"t3_bps must be in [0, {BPS_DENOM}]: {self.t3_bps}")
        if not (self.t1_bps <= self.t2_bps <= self.t3_bps):
            raise ValueError(
                f"thresholds must be ordered: t1={self.t1_bps} <= t2={self.t2_bps} <= t3={self.t3_bps}"
            )


@dataclass(frozen=True)
class TierEffects:
    """Post-state observables from a tier observation."""

    tier_out: int
    fee_mult_bps: int
    max_trade_bps: int
    halt: bool

    def __post_init__(self) -> None:
        for name, val in (
            ("tier_out", self.tier_out),
            ("fee_mult_bps", self.fee_mult_bps),
            ("max_trade_bps", self.max_trade_bps),
        ):
            if not isinstance(val, int) or isinstance(val, bool):
                raise TypeError(f"{name} must be an int")
        if not isinstance(self.halt, bool):
            raise TypeError("halt must be a bool")


# Fee multiplier lookup: tier → bps-of-base (10000 = 1x)
_FEE_MULT_BPS = {0: 10000, 1: 20000, 2: 30000, 3: 0}

# Max trade cap lookup: tier → bps-of-reserves (10000 = 100%)
_MAX_TRADE_BPS = {0: 10000, 1: 10000, 2: 1000, 3: 0}


def tier_effects(tier: int) -> TierEffects:
    """Compute effects for a given tier value."""
    if not (0 <= tier <= 3):
        raise ValueError(f"tier must be in [0, 3]: {tier}")
    return TierEffects(
        tier_out=tier,
        fee_mult_bps=_FEE_MULT_BPS[tier],
        max_trade_bps=_MAX_TRADE_BPS[tier],
        halt=(tier == 3),
    )
