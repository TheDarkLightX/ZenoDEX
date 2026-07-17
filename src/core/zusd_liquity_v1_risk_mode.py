"""Pure source-pinned Liquity V1 system risk-mode kernel.

This profile-specific module intentionally does not reuse the generic
SimplexBorrow TCR helper. Liquity V1 derives system collateral and debt from the
Active Pool plus Default Pool only, then compares the exact E18 collateral ratio
to the fixed 150% CCR. Stability Pool, Gas Pool, borrower surplus, wallets, and
fee custody are outside this relation.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

DECIMAL_PRECISION_E18 = 1_000_000_000_000_000_000
BPS_TO_E18 = 100_000_000_000_000
LIQUITY_V1_MCR_BPS = 11_000
LIQUITY_V1_CCR_BPS = 15_000
LIQUITY_V1_CCR_E18 = LIQUITY_V1_CCR_BPS * BPS_TO_E18
MAX_U256 = (1 << 256) - 1
MAX_U512 = (1 << 512) - 1


def _require_u256(name: str, value: object, *, positive: bool = False) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    minimum = 1 if positive else 0
    if value < minimum:
        qualifier = "positive" if positive else "non-negative"
        raise ValueError(f"{name} must be {qualifier}")
    if value > MAX_U256:
        raise ValueError(f"{name} exceeds U256")
    return value


def _checked_add_u256(name: str, left: int, right: int) -> int:
    out = left + right
    if out > MAX_U256:
        raise ValueError(f"{name} exceeds U256")
    return out


def _checked_mul_u512(name: str, left: int, right: int) -> int:
    out = left * right
    if out > MAX_U512:
        raise ValueError(f"{name} exceeds U512")
    return out


@dataclass(frozen=True, slots=True, order=True)
class CollateralSourceAtoms:
    value: int

    def __post_init__(self) -> None:
        _require_u256("collateral_source_atoms", self.value)


@dataclass(frozen=True, slots=True, order=True)
class ZusdSourceAtoms:
    value: int

    def __post_init__(self) -> None:
        _require_u256("zusd_source_atoms", self.value)


@dataclass(frozen=True, slots=True, order=True)
class PriceSourceE18:
    value: int

    def __post_init__(self) -> None:
        _require_u256("price_source_e18", self.value, positive=True)


@dataclass(frozen=True, slots=True)
class LiquityV1SystemPools:
    """Exactly the Active and Default Pool risk-bearing balances."""

    active_collateral: CollateralSourceAtoms
    active_debt: ZusdSourceAtoms
    default_collateral: CollateralSourceAtoms
    default_debt: ZusdSourceAtoms

    def __post_init__(self) -> None:
        if type(self.active_collateral) is not CollateralSourceAtoms:
            raise TypeError("active_collateral must be CollateralSourceAtoms")
        if type(self.active_debt) is not ZusdSourceAtoms:
            raise TypeError("active_debt must be ZusdSourceAtoms")
        if type(self.default_collateral) is not CollateralSourceAtoms:
            raise TypeError("default_collateral must be CollateralSourceAtoms")
        if type(self.default_debt) is not ZusdSourceAtoms:
            raise TypeError("default_debt must be ZusdSourceAtoms")

    @property
    def total_collateral(self) -> CollateralSourceAtoms:
        return CollateralSourceAtoms(
            _checked_add_u256(
                "total_system_collateral_source",
                self.active_collateral.value,
                self.default_collateral.value,
            )
        )

    @property
    def total_debt(self) -> ZusdSourceAtoms:
        return ZusdSourceAtoms(
            _checked_add_u256(
                "total_system_debt_source",
                self.active_debt.value,
                self.default_debt.value,
            )
        )


class LiquityV1RiskMode(str, Enum):
    NORMAL = "normal"
    RECOVERY = "recovery"


@dataclass(frozen=True, slots=True)
class LiquityV1RiskDecision:
    total_collateral_source: CollateralSourceAtoms
    total_debt_source: ZusdSourceAtoms
    price_source_e18: PriceSourceE18
    collateral_value_source: int
    tcr_e18: int
    mode: LiquityV1RiskMode

    def __post_init__(self) -> None:
        if type(self.total_collateral_source) is not CollateralSourceAtoms:
            raise TypeError("total_collateral_source must be CollateralSourceAtoms")
        if type(self.total_debt_source) is not ZusdSourceAtoms:
            raise TypeError("total_debt_source must be ZusdSourceAtoms")
        if type(self.price_source_e18) is not PriceSourceE18:
            raise TypeError("price_source_e18 must be PriceSourceE18")
        collateral_value = _require_u256(
            "collateral_value_source",
            self.collateral_value_source,
        )
        tcr = _require_u256("tcr_e18", self.tcr_e18)
        if type(self.mode) is not LiquityV1RiskMode:
            raise TypeError("mode must be LiquityV1RiskMode")

        expected_collateral_value, expected_tcr, expected_mode = _derive_values(
            total_collateral=self.total_collateral_source,
            total_debt=self.total_debt_source,
            price=self.price_source_e18,
        )
        if collateral_value != expected_collateral_value:
            raise ValueError("collateral value is inconsistent")
        if tcr != expected_tcr:
            raise ValueError("TCR is inconsistent")
        if self.mode is not expected_mode:
            raise ValueError("risk mode is inconsistent")

    @property
    def ccr_e18(self) -> int:
        return LIQUITY_V1_CCR_E18


def _derive_values(
    *,
    total_collateral: CollateralSourceAtoms,
    total_debt: ZusdSourceAtoms,
    price: PriceSourceE18,
) -> tuple[int, int, LiquityV1RiskMode]:
    collateral_product = _checked_mul_u512(
        "system_collateral_price_product",
        total_collateral.value,
        price.value,
    )
    collateral_value = collateral_product // DECIMAL_PRECISION_E18
    if collateral_value > MAX_U256:
        raise ValueError("collateral_value_source exceeds U256")

    if total_debt.value == 0:
        return collateral_value, MAX_U256, LiquityV1RiskMode.NORMAL

    ratio_product = _checked_mul_u512(
        "system_collateral_ratio_product",
        total_collateral.value,
        price.value,
    )
    tcr_e18 = ratio_product // total_debt.value
    if tcr_e18 > MAX_U256:
        raise ValueError("tcr_e18 exceeds U256")
    mode = (
        LiquityV1RiskMode.RECOVERY
        if tcr_e18 < LIQUITY_V1_CCR_E18
        else LiquityV1RiskMode.NORMAL
    )
    return collateral_value, tcr_e18, mode


def derive_liquity_v1_risk_mode(
    *,
    pools: LiquityV1SystemPools,
    price: PriceSourceE18,
) -> LiquityV1RiskDecision:
    """Derive, never store, the unique exact Liquity V1 system risk mode."""

    if type(pools) is not LiquityV1SystemPools:
        raise TypeError("pools must be LiquityV1SystemPools")
    if type(price) is not PriceSourceE18:
        raise TypeError("price must be PriceSourceE18")

    total_collateral = pools.total_collateral
    total_debt = pools.total_debt
    collateral_value, tcr_e18, mode = _derive_values(
        total_collateral=total_collateral,
        total_debt=total_debt,
        price=price,
    )
    return LiquityV1RiskDecision(
        total_collateral_source=total_collateral,
        total_debt_source=total_debt,
        price_source_e18=price,
        collateral_value_source=collateral_value,
        tcr_e18=tcr_e18,
        mode=mode,
    )
