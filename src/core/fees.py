"""
Fee splitting kernels (deterministic, integer-only).

The primary pattern here is **dust-carry**: rounding remainders are carried
forward so value is never stranded across repeated splits.
"""

from __future__ import annotations

from dataclasses import dataclass


BPS_DENOM = 10_000


@dataclass(frozen=True)
class FeeSplitParams:
    buyback_bps: int
    treasury_bps: int
    rewards_bps: int

    def __post_init__(self) -> None:
        for name, v in (
            ("buyback_bps", self.buyback_bps),
            ("treasury_bps", self.treasury_bps),
            ("rewards_bps", self.rewards_bps),
        ):
            if not isinstance(v, int) or isinstance(v, bool):
                raise TypeError(f"{name} must be an int")
            if not (0 <= v <= BPS_DENOM):
                raise ValueError(f"{name} must be in [0, {BPS_DENOM}]: {v}")
        total = self.buyback_bps + self.treasury_bps + self.rewards_bps
        if total != BPS_DENOM:
            raise ValueError(f"bps must sum to {BPS_DENOM}, got {total}")


@dataclass(frozen=True)
class FeeSplitResult:
    buyback_amount: int
    treasury_amount: int
    rewards_amount: int
    dust_carried: int

    def __post_init__(self) -> None:
        for name, v in (
            ("buyback_amount", self.buyback_amount),
            ("treasury_amount", self.treasury_amount),
            ("rewards_amount", self.rewards_amount),
            ("dust_carried", self.dust_carried),
        ):
            if not isinstance(v, int) or isinstance(v, bool):
                raise TypeError(f"{name} must be an int")
            if v < 0:
                raise ValueError(f"{name} must be non-negative: {v}")


@dataclass(frozen=True)
class FeeAccumulatorState:
    """Carries rounding dust in fee units (not scaled)."""

    dust: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.dust, int) or isinstance(self.dust, bool):
            raise TypeError("dust must be an int")
        if self.dust < 0:
            raise ValueError("dust must be non-negative")


def split_fee_with_dust_carry(
    fee_amount: int,
    params: FeeSplitParams,
    state: FeeAccumulatorState = FeeAccumulatorState(),
) -> tuple[FeeSplitResult, FeeAccumulatorState]:
    """
    Split `fee_amount` across (buyback, treasury, rewards) with deterministic floor rounding.

    Remainders are carried in `state.dust` and added to the next split.
    """
    if not isinstance(fee_amount, int) or isinstance(fee_amount, bool) or fee_amount < 0:
        raise ValueError(f"fee_amount must be a non-negative int, got {fee_amount}")

    total = fee_amount + state.dust
    buyback = (total * params.buyback_bps) // BPS_DENOM
    treasury = (total * params.treasury_bps) // BPS_DENOM
    rewards = (total * params.rewards_bps) // BPS_DENOM
    distributed = buyback + treasury + rewards
    if distributed > total:
        raise AssertionError("fee split over-distributed")
    dust = total - distributed

    return (
        FeeSplitResult(
            buyback_amount=buyback,
            treasury_amount=treasury,
            rewards_amount=rewards,
            dust_carried=dust,
        ),
        FeeAccumulatorState(dust=dust),
    )

