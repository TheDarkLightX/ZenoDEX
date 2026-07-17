"""Pure canonical-zUSD free-debt liability composition.

The integration shell extracts each authoritative custody domain into this
typed value. This module owns only the dimension-safe accounting relation; it
does not decide whether the shell's inventory of custody domains is complete.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

MAX_U256 = (1 << 256) - 1


def _require_u256(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if value > MAX_U256:
        raise ValueError(f"{name} exceeds U256")
    return value


def _checked_sum_u256(name: str, values: tuple[int, ...]) -> int:
    total = 0
    for value in values:
        total += value
        if total > MAX_U256:
            raise ValueError(f"{name} exceeds U256")
    return total


@dataclass(frozen=True, slots=True)
class ZUSDFreeDebtLiabilityBreakdown:
    """Enumerated free canonical-zUSD custody and liability domains.

    Gas Pool custody is explicit because each active Liquity-minimum vault owns
    one fixed zUSD reserve that later transfers to its liquidation keeper
    without minting or burning supply.
    """

    wallet_e8: int
    dex_pool_e8: int
    perps_e8: int
    protocol_fee_reserve_e8: int
    staking_fee_pool_e8: int
    host_fee_pool_e8: int
    gas_pool_reserve_e8: int

    def __post_init__(self) -> None:
        values = tuple(
            _require_u256(field_name, getattr(self, field_name))
            for field_name in self.__dataclass_fields__
        )
        _checked_sum_u256("free_debt_liability_total_e8", values)

    @property
    def total_e8(self) -> int:
        return _checked_sum_u256(
            "free_debt_liability_total_e8",
            (
                self.wallet_e8,
                self.dex_pool_e8,
                self.perps_e8,
                self.protocol_fee_reserve_e8,
                self.staking_fee_pool_e8,
                self.host_fee_pool_e8,
                self.gas_pool_reserve_e8,
            ),
        )


class ZUSDLiabilityCoverCode(str, Enum):
    COVERED = "covered"
    FREE_DEBT_MISMATCH = "free_debt_mismatch"


@dataclass(frozen=True, slots=True)
class ZUSDLiabilityCoverDecision:
    code: ZUSDLiabilityCoverCode
    expected_free_debt_e8: int
    actual_free_debt_e8: int

    def __post_init__(self) -> None:
        if type(self.code) is not ZUSDLiabilityCoverCode:
            raise TypeError("code must be a ZUSDLiabilityCoverCode")
        _require_u256("expected_free_debt_e8", self.expected_free_debt_e8)
        _require_u256("actual_free_debt_e8", self.actual_free_debt_e8)
        if (self.code is ZUSDLiabilityCoverCode.COVERED) != (
            self.expected_free_debt_e8 == self.actual_free_debt_e8
        ):
            raise ValueError("liability-cover decision code is inconsistent")

    @property
    def covered(self) -> bool:
        return self.code is ZUSDLiabilityCoverCode.COVERED


def evaluate_zusd_free_debt_liability_cover(
    *,
    breakdown: ZUSDFreeDebtLiabilityBreakdown,
    actual_free_debt_e8: int,
) -> ZUSDLiabilityCoverDecision:
    """Evaluate exact cover without mutation, I/O, clocks, or hidden state."""

    if type(breakdown) is not ZUSDFreeDebtLiabilityBreakdown:
        raise TypeError("breakdown must be a ZUSDFreeDebtLiabilityBreakdown")
    actual = _require_u256("actual_free_debt_e8", actual_free_debt_e8)
    expected = breakdown.total_e8
    code = (
        ZUSDLiabilityCoverCode.COVERED
        if expected == actual
        else ZUSDLiabilityCoverCode.FREE_DEBT_MISMATCH
    )
    return ZUSDLiabilityCoverDecision(
        code=code,
        expected_free_debt_e8=expected,
        actual_free_debt_e8=actual,
    )
