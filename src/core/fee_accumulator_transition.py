"""Exact fee dust-carry transition over committed FCIS state."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, final

from ..state.state_snapshot_values import CommittedFeeAccumulatorStateV1
from .fees import BPS_DENOM, FeeSplitParams, FeeSplitResult, _split_fee_amounts_v1


class FeeAccumulatorTransitionCodeV1(Enum):
    """Stable reject classes for exact fee allocation."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    OUT_OF_RANGE = "out_of_range"
    INVALID_PRESTATE = "invalid_prestate"
    INVALID_PARAMETERS = "invalid_parameters"
    CONSERVATION = "conservation"


@final
@dataclass(frozen=True, slots=True)
class FeeAccumulatorTransitionRejectV1:
    """Typed no-candidate rejection for fee allocation."""

    code: FeeAccumulatorTransitionCodeV1
    field: str

    def __post_init__(self) -> None:
        if type(self.code) is not FeeAccumulatorTransitionCodeV1:
            raise TypeError("fee transition rejection code must be exact")
        if type(self.field) is not str or not self.field:
            raise TypeError("fee transition rejection field must be exact")


@final
@dataclass(frozen=True, slots=True)
class FeeAccumulatorTransitionOkV1:
    """One allocation and the exact accumulator successor that produced it."""

    allocation: FeeSplitResult
    state: CommittedFeeAccumulatorStateV1

    def __post_init__(self) -> None:
        if type(self.allocation) is not FeeSplitResult:
            raise TypeError("fee allocation must be an exact FeeSplitResult")
        if type(self.state) is not CommittedFeeAccumulatorStateV1:
            raise TypeError("fee successor must be exact committed state")


FeeAccumulatorTransitionResultV1: TypeAlias = (
    FeeAccumulatorTransitionOkV1 | FeeAccumulatorTransitionRejectV1
)


def _reject(
    code: FeeAccumulatorTransitionCodeV1,
    field: str,
) -> FeeAccumulatorTransitionRejectV1:
    return FeeAccumulatorTransitionRejectV1(code, field)


def _validated_dust(
    state: object,
) -> int | FeeAccumulatorTransitionRejectV1:
    if type(state) is not CommittedFeeAccumulatorStateV1:
        return _reject(FeeAccumulatorTransitionCodeV1.WRONG_EXACT_TYPE, "state")
    try:
        dust = object.__getattribute__(state, "dust")
    except AttributeError:
        return _reject(FeeAccumulatorTransitionCodeV1.INVALID_PRESTATE, "state.dust")
    if type(dust) is not int or dust < 0:
        return _reject(FeeAccumulatorTransitionCodeV1.INVALID_PRESTATE, "state.dust")
    return dust


def _validated_params(
    params: object,
) -> tuple[int, int, int] | FeeAccumulatorTransitionRejectV1:
    if type(params) is not FeeSplitParams:
        return _reject(FeeAccumulatorTransitionCodeV1.WRONG_EXACT_TYPE, "params")
    values: list[int] = []
    for field in ("buyback_bps", "treasury_bps", "rewards_bps"):
        try:
            value = object.__getattribute__(params, field)
        except AttributeError:
            return _reject(FeeAccumulatorTransitionCodeV1.INVALID_PARAMETERS, field)
        if type(value) is not int or not 0 <= value <= BPS_DENOM:
            return _reject(FeeAccumulatorTransitionCodeV1.INVALID_PARAMETERS, field)
        values.append(value)
    if sum(values) != BPS_DENOM:
        return _reject(FeeAccumulatorTransitionCodeV1.INVALID_PARAMETERS, "params.total")
    return values[0], values[1], values[2]


def split_fee_with_committed_dust_carry_v1(
    *,
    fee_amount: object,
    params: object,
    state: object,
) -> FeeAccumulatorTransitionResultV1:
    """Split once using exact integers and retain the exact state candidate."""

    if type(fee_amount) is not int:
        return _reject(FeeAccumulatorTransitionCodeV1.WRONG_EXACT_TYPE, "fee_amount")
    if fee_amount < 0:
        return _reject(FeeAccumulatorTransitionCodeV1.OUT_OF_RANGE, "fee_amount")
    dust = _validated_dust(state)
    if type(dust) is FeeAccumulatorTransitionRejectV1:
        return dust
    split_params = _validated_params(params)
    if type(split_params) is FeeAccumulatorTransitionRejectV1:
        return split_params
    buyback_bps, treasury_bps, rewards_bps = split_params

    total = fee_amount + dust
    try:
        buyback, treasury, rewards, next_dust = _split_fee_amounts_v1(
            total=total,
            buyback_bps=buyback_bps,
            treasury_bps=treasury_bps,
            rewards_bps=rewards_bps,
        )
    except ArithmeticError:
        return _reject(FeeAccumulatorTransitionCodeV1.CONSERVATION, "distributed")

    return FeeAccumulatorTransitionOkV1(
        allocation=FeeSplitResult(
            buyback_amount=buyback,
            treasury_amount=treasury,
            rewards_amount=rewards,
            dust_carried=next_dust,
        ),
        state=CommittedFeeAccumulatorStateV1(dust=next_dust),
    )


__all__ = [
    "FeeAccumulatorTransitionCodeV1",
    "FeeAccumulatorTransitionOkV1",
    "FeeAccumulatorTransitionRejectV1",
    "FeeAccumulatorTransitionResultV1",
    "split_fee_with_committed_dust_carry_v1",
]
