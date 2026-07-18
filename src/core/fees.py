"""
Fee splitting kernels (deterministic, integer-only).

The primary pattern here is **dust-carry**: rounding remainders are carried
forward so value is never stranded across repeated splits.
"""

from __future__ import annotations

from dataclasses import dataclass


BPS_DENOM = 10_000
FEE_SPLIT_LANE_COUNT = 3
MAX_FEE_SPLIT_DUST = FEE_SPLIT_LANE_COUNT - 1


@dataclass(frozen=True, slots=True)
class FeeSplitParams:
    buyback_bps: int
    treasury_bps: int
    rewards_bps: int

    def __post_init__(self) -> None:
        for name, value in (
            ("buyback_bps", self.buyback_bps),
            ("treasury_bps", self.treasury_bps),
            ("rewards_bps", self.rewards_bps),
        ):
            if type(value) is not int:
                raise TypeError(f"{name} must be an int")
            if not 0 <= value <= BPS_DENOM:
                raise ValueError(f"{name} must be in [0, {BPS_DENOM}]: {value}")
        total = self.buyback_bps + self.treasury_bps + self.rewards_bps
        if total != BPS_DENOM:
            raise ValueError(f"bps must sum to {BPS_DENOM}, got {total}")


@dataclass(frozen=True, slots=True)
class FeeSplitResult:
    buyback_amount: int
    treasury_amount: int
    rewards_amount: int
    dust_carried: int

    def __post_init__(self) -> None:
        for name, value in (
            ("buyback_amount", self.buyback_amount),
            ("treasury_amount", self.treasury_amount),
            ("rewards_amount", self.rewards_amount),
            ("dust_carried", self.dust_carried),
        ):
            if type(value) is not int:
                raise TypeError(f"{name} must be an int")
            if value < 0:
                raise ValueError(f"{name} must be non-negative: {value}")
        if self.dust_carried > MAX_FEE_SPLIT_DUST:
            raise ValueError(
                "dust_carried exceeds the three-lane floor-rounding bound: "
                f"{self.dust_carried} > {MAX_FEE_SPLIT_DUST}"
            )


@dataclass(frozen=True, slots=True)
class FeeAccumulatorState:
    """Carries at most two whole fee atoms between three-lane splits."""

    dust: int = 0

    def __post_init__(self) -> None:
        if type(self.dust) is not int:
            raise TypeError("dust must be an int")
        if not 0 <= self.dust <= MAX_FEE_SPLIT_DUST:
            raise ValueError(
                "dust must be in the inductive three-lane bound "
                f"[0, {MAX_FEE_SPLIT_DUST}]"
            )


def split_fee_with_dust_carry(
    fee_amount: int,
    params: FeeSplitParams,
    state: FeeAccumulatorState = FeeAccumulatorState(),
) -> tuple[FeeSplitResult, FeeAccumulatorState]:
    """Split one fee and carry the bounded floor-rounding remainder.

    Exact core types are required so a caller cannot substitute behavior-changing
    subclasses or look-alike objects at the committed arithmetic boundary.
    """
    if type(fee_amount) is not int or fee_amount < 0:
        raise ValueError(f"fee_amount must be a non-negative int, got {fee_amount}")
    if type(params) is not FeeSplitParams:
        raise TypeError("params must be an exact FeeSplitParams")
    if type(state) is not FeeAccumulatorState:
        raise TypeError("state must be an exact FeeAccumulatorState")

    total = fee_amount + state.dust
    buyback = (total * params.buyback_bps) // BPS_DENOM
    treasury = (total * params.treasury_bps) // BPS_DENOM
    rewards = (total * params.rewards_bps) // BPS_DENOM
    distributed = buyback + treasury + rewards
    if distributed > total:
        raise AssertionError("fee split over-distributed")
    dust = total - distributed
    if dust > MAX_FEE_SPLIT_DUST:
        raise AssertionError("three-lane floor-rounding dust bound violated")

    result = FeeSplitResult(
        buyback_amount=buyback,
        treasury_amount=treasury,
        rewards_amount=rewards,
        dust_carried=dust,
    )
    return result, FeeAccumulatorState(dust=dust)
