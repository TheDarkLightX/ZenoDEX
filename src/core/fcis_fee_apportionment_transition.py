"""Overflow-safe U256 quota arithmetic for the unmounted FCIS fee kernel."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import final

from .fcis_fee_apportionment_values import (
    BPS_DENOMINATOR_V2,
    MAX_FEE_AMOUNT_V2,
)


class FeeQuotaRejectCodeV2(Enum):
    """Closed rejection classes for the quota primitive."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    UNSUPPORTED_DENOMINATOR = "unsupported_denominator"
    AMOUNT_OUT_OF_RANGE = "amount_out_of_range"
    WEIGHT_OUT_OF_RANGE = "weight_out_of_range"
    INTERNAL_RELATION_FAILURE = "internal_relation_failure"


@final
@dataclass(frozen=True, slots=True)
class FeeQuotaV2:
    """One exact Euclidean quota decomposition in the production BPS domain."""

    amount: int
    weight: int
    denominator: int
    quotient: int
    residual: int
    base: int
    remainder: int

    def __post_init__(self) -> None:
        fields = (
            self.amount,
            self.weight,
            self.denominator,
            self.quotient,
            self.residual,
            self.base,
            self.remainder,
        )
        if any(type(value) is not int for value in fields):
            raise TypeError("fee quota fields must be exact integers")
        if self.denominator != BPS_DENOMINATOR_V2:
            raise ValueError("fee quota denominator is not the production profile")
        if not 0 <= self.amount <= MAX_FEE_AMOUNT_V2:
            raise ValueError("fee quota amount is outside the U256 domain")
        if not 0 <= self.weight <= self.denominator:
            raise ValueError("fee quota weight is outside the BPS domain")
        if self.quotient < 0 or self.residual < 0:
            raise ValueError("fee quota Euclidean components must be nonnegative")
        quotient, residual = divmod(self.amount, self.denominator)
        if (self.quotient, self.residual) != (quotient, residual):
            raise ValueError("fee quota Euclidean decomposition is inconsistent")
        if self.residual >= self.denominator:
            raise ValueError("fee quota residual is outside the denominator range")

        residual_product = self.residual * self.weight
        expected_base = (
            self.quotient * self.weight
            + residual_product // self.denominator
        )
        expected_remainder = residual_product % self.denominator
        if (self.base, self.remainder) != (expected_base, expected_remainder):
            raise ValueError("fee quota decomposition is inconsistent")
        if self.quotient * self.weight > self.amount:
            raise ValueError("fee quota quotient product exceeds its amount")
        if residual_product >= self.denominator * self.denominator:
            raise ValueError("fee quota residual product exceeds its width bound")
        if not 0 <= self.remainder < self.denominator:
            raise ValueError("fee quota remainder is outside the denominator range")
        if not 0 <= self.base <= self.amount:
            raise ValueError("fee quota base is outside its amount bound")


@final
@dataclass(frozen=True, slots=True)
class FeeQuotaRejectV2:
    """Typed, fail-closed rejection for invalid quota inputs."""

    code: FeeQuotaRejectCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not FeeQuotaRejectCodeV2:
            raise TypeError("fee quota rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("fee quota rejection path must be exact")


FeeQuotaResultV2 = FeeQuotaV2 | FeeQuotaRejectV2


def _reject_v2(
    code: FeeQuotaRejectCodeV2,
    path: tuple[str, ...],
) -> FeeQuotaRejectV2:
    return FeeQuotaRejectV2(code, path)


def compute_fee_quota_v2(
    *,
    amount: object,
    weight: object,
    denominator: object = BPS_DENOMINATOR_V2,
) -> FeeQuotaResultV2:
    """Compute ``base`` and ``remainder`` without forming ``amount * weight``."""

    if type(amount) is not int:
        return _reject_v2(
            FeeQuotaRejectCodeV2.WRONG_EXACT_TYPE,
            ("amount",),
        )
    if type(weight) is not int:
        return _reject_v2(
            FeeQuotaRejectCodeV2.WRONG_EXACT_TYPE,
            ("weight",),
        )
    if type(denominator) is not int:
        return _reject_v2(
            FeeQuotaRejectCodeV2.WRONG_EXACT_TYPE,
            ("denominator",),
        )
    if denominator != BPS_DENOMINATOR_V2:
        return _reject_v2(
            FeeQuotaRejectCodeV2.UNSUPPORTED_DENOMINATOR,
            ("denominator",),
        )
    if not 0 <= amount <= MAX_FEE_AMOUNT_V2:
        return _reject_v2(
            FeeQuotaRejectCodeV2.AMOUNT_OUT_OF_RANGE,
            ("amount",),
        )
    if not 0 <= weight <= denominator:
        return _reject_v2(
            FeeQuotaRejectCodeV2.WEIGHT_OUT_OF_RANGE,
            ("weight",),
        )

    quotient, residual = divmod(amount, denominator)
    residual_product = residual * weight
    base = quotient * weight + residual_product // denominator
    remainder = residual_product % denominator
    try:
        return FeeQuotaV2(
            amount=amount,
            weight=weight,
            denominator=denominator,
            quotient=quotient,
            residual=residual,
            base=base,
            remainder=remainder,
        )
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v2(
            FeeQuotaRejectCodeV2.INTERNAL_RELATION_FAILURE,
            ("relation",),
        )


__all__ = (
    "FeeQuotaRejectCodeV2",
    "FeeQuotaRejectV2",
    "FeeQuotaResultV2",
    "FeeQuotaV2",
    "compute_fee_quota_v2",
)
