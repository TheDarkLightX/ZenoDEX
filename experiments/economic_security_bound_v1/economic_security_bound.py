"""Application economic-security bound (resilience gap #2): make the
"fees-in-pool are recapturable" insight a NUMBER.

Insight (CLAUDE.md / perp-incentives): a protocol fee that flows into the pool is
**recapturable** by an attacker who also holds LP share. An attacker with LP share
alpha recaptures alpha of any fee they pay, so the fee's *deterrence* is only the
**non-recapturable** remainder `fee * (1 - alpha)`. Only genuinely non-recapturable
costs (gas, locked collateral, slashing) deter robustly.

This module turns that into an exact, integer, falsifiable model and pins the
load-bearing result with a tightness witness:

    THEOREM (robust deterrence). An attack of value V is deterred for EVERY LP
    share alpha in [0, 1]  iff  (gas + collateral) >= V.
    (Fee provides at most `fee*(1-alpha)` of deterrence, which is 0 at alpha=1, so
    the worst case alpha=1 forces gas+collateral >= V; and that suffices for all
    alpha since fee*(1-alpha) >= 0. The bound is tight: at alpha=1 the fee is fully
    recaptured and contributes nothing.)

All quantities are integers in base units; LP share and fee are basis points
(0..10000) so the core is float-free and consensus-style. Pure / deterministic.
"""

from __future__ import annotations

from dataclasses import dataclass

BPS = 10_000


def _check_bps(value: int, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if not (0 <= value <= BPS):
        raise ValueError(f"{name} must be in [0, {BPS}] bps")
    return value


def _check_nonneg(value: int, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be >= 0")
    return value


def fee_paid(notional: int, fee_bps: int) -> int:
    """Protocol fee paid on a trade of `notional`, floor (the fee that lands in the pool)."""
    _check_nonneg(notional, "notional")
    _check_bps(fee_bps, "fee_bps")
    return notional * fee_bps // BPS


def recaptured_fee(fee_amount: int, alpha_bps: int) -> int:
    """The portion of a paid fee an attacker with LP share `alpha_bps` recaptures
    (they own alpha of the pool the fee accrues to). Floor."""
    _check_nonneg(fee_amount, "fee_amount")
    _check_bps(alpha_bps, "alpha_bps")
    return fee_amount * alpha_bps // BPS


def non_recapturable_fee_cost(fee_amount: int, alpha_bps: int) -> int:
    """The deterring part of a fee: `fee - recaptured` = the share that does NOT
    flow back to the attacker. Equals `ceil(fee * (1 - alpha))` by complementation."""
    return fee_amount - recaptured_fee(fee_amount, alpha_bps)


def fee_deterrence_efficiency_bps(alpha_bps: int) -> int:
    """Fraction (in bps) of a nominal fee that actually deters: `10000 - alpha_bps`.
    100% at alpha=0, 10% at alpha=9000, 0% at alpha=10000 (full recapture)."""
    return BPS - _check_bps(alpha_bps, "alpha_bps")


@dataclass(frozen=True)
class AttackModel:
    """An extraction attempt. All amounts in integer base units; bps for rates."""
    v_attack: int          # value the attacker extracts if the attack succeeds
    fee_notional: int      # notional the attack routes through (the fee base)
    fee_bps: int           # protocol fee rate
    alpha_bps: int         # attacker's LP share of the pool the fee accrues to
    gas: int               # non-recapturable execution cost
    collateral: int        # non-recapturable locked-collateral / slashing cost

    def __post_init__(self) -> None:
        _check_nonneg(self.v_attack, "v_attack")
        _check_nonneg(self.fee_notional, "fee_notional")
        _check_bps(self.fee_bps, "fee_bps")
        _check_bps(self.alpha_bps, "alpha_bps")
        _check_nonneg(self.gas, "gas")
        _check_nonneg(self.collateral, "collateral")

    def fee(self) -> int:
        return fee_paid(self.fee_notional, self.fee_bps)

    def deterrence_cost(self) -> int:
        """Total NON-RECAPTURABLE cost the attacker actually eats."""
        return non_recapturable_fee_cost(self.fee(), self.alpha_bps) + self.gas + self.collateral

    def net_profit(self) -> int:
        return self.v_attack - self.deterrence_cost()

    def is_profitable(self) -> bool:
        """Attack pays off: extracted value exceeds the non-recapturable cost."""
        return self.net_profit() > 0


def min_non_recapturable_to_deter(v_attack: int, fee_amount: int, alpha_bps: int) -> int:
    """Minimum (gas + collateral) needed to deter, given the fee's residual deterrence.
    = max(0, V - fee*(1-alpha)). At alpha=10000 this is exactly V (fee deters nothing)."""
    _check_nonneg(v_attack, "v_attack")
    residual = non_recapturable_fee_cost(_check_nonneg(fee_amount, "fee_amount"), alpha_bps)
    return max(0, v_attack - residual)


def deters_for_all_alpha(v_attack: int, gas: int, collateral: int) -> bool:
    """The robust-deterrence THEOREM: deters every LP share iff non-recapturable
    cost alone covers V (the fee is treated as zero deterrence — its worst case)."""
    _check_nonneg(v_attack, "v_attack")
    _check_nonneg(gas, "gas")
    _check_nonneg(collateral, "collateral")
    return gas + collateral >= v_attack
