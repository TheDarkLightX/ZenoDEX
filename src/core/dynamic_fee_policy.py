"""Deterministic dynamic fee policies (UX + security experiments).

This is not consensus-critical. It is intended to support:
- Sandwich-risk simulations and UI warnings.
- Candidate mechanism design for future dynamic-fee pool upgrades (if adopted).

Design goals:
- Deterministic integer-only computation.
- Explicit bounds (min/max fee).
- Simple monotone response to a "stress" proxy (trade size vs reserves).
"""

from __future__ import annotations

from dataclasses import dataclass


def _require_plain_int(name: str, value: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


@dataclass(frozen=True)
class StressFeePolicy:
    """Piecewise-linear fee schedule in bps as a function of trade stress.

    stress_bps := clamp(amount_in / reserve_in, [0,1]) in bps (0..10_000)
    fee_bps := clamp(base_fee + slope_bps * stress_bps / 10_000, [min_fee, max_fee])
    """

    base_fee_bps: int
    slope_bps: int
    min_fee_bps: int = 0
    max_fee_bps: int = 10_000

    def __post_init__(self) -> None:
        for name, v in (
            ("base_fee_bps", self.base_fee_bps),
            ("slope_bps", self.slope_bps),
            ("min_fee_bps", self.min_fee_bps),
            ("max_fee_bps", self.max_fee_bps),
        ):
            if not isinstance(v, int) or isinstance(v, bool):
                raise TypeError(f"{name} must be an int")
        if not (0 <= self.base_fee_bps <= 10_000):
            raise ValueError("base_fee_bps must be in [0, 10000]")
        if self.slope_bps < 0:
            raise ValueError("slope_bps must be non-negative")
        if not (0 <= self.min_fee_bps <= 10_000):
            raise ValueError("min_fee_bps must be in [0, 10000]")
        if not (0 <= self.max_fee_bps <= 10_000):
            raise ValueError("max_fee_bps must be in [0, 10000]")
        if self.min_fee_bps > self.max_fee_bps:
            raise ValueError("min_fee_bps must be <= max_fee_bps")


def fee_bps_from_stress_policy(
    policy: StressFeePolicy,
    *,
    reserve_in: int,
    amount_in: int,
) -> int:
    """Compute stress-based fee in bps (integer-only, deterministic)."""
    reserve = _require_plain_int("reserve_in", reserve_in)
    amount = _require_plain_int("amount_in", amount_in)
    if reserve <= 0:
        raise ValueError("reserve_in must be positive")
    if amount < 0:
        raise ValueError("amount_in must be non-negative")

    stress_bps = (amount * 10_000) // reserve
    if stress_bps > 10_000:
        stress_bps = 10_000

    fee = int(policy.base_fee_bps) + (int(stress_bps) * int(policy.slope_bps)) // 10_000
    if fee < int(policy.min_fee_bps):
        fee = int(policy.min_fee_bps)
    if fee > int(policy.max_fee_bps):
        fee = int(policy.max_fee_bps)
    return int(fee)
