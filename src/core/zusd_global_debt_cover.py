"""Pure global canonical-zUSD debt and custody cover decision.

This module composes the enumerated free-debt liability inventory with Stability
Pool escrow. It returns every failed equality in a canonical order so callers
do not lose independent diagnostics after the first mismatch.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from .zusd_liability_cover import (
    MAX_U256,
    ZUSDFreeDebtLiabilityBreakdown,
)


def _require_u256(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if value > MAX_U256:
        raise ValueError(f"{name} exceeds U256")
    return value


def _checked_add_u256(name: str, left: int, right: int) -> int:
    out = left + right
    if out > MAX_U256:
        raise ValueError(f"{name} exceeds U256")
    return out


class ZUSDGlobalDebtCoverViolation(str, Enum):
    FREE_DEBT_LIABILITY_MISMATCH = "free_debt_liability_mismatch"
    STABILITY_POOL_CUSTODY_MISMATCH = "stability_pool_custody_mismatch"
    CORE_DEBT_SPLIT_MISMATCH = "core_debt_split_mismatch"
    GLOBAL_DEBT_LIABILITY_MISMATCH = "global_debt_liability_mismatch"


_VIOLATION_ORDER = (
    ZUSDGlobalDebtCoverViolation.FREE_DEBT_LIABILITY_MISMATCH,
    ZUSDGlobalDebtCoverViolation.STABILITY_POOL_CUSTODY_MISMATCH,
    ZUSDGlobalDebtCoverViolation.CORE_DEBT_SPLIT_MISMATCH,
    ZUSDGlobalDebtCoverViolation.GLOBAL_DEBT_LIABILITY_MISMATCH,
)


def _derive_violations(
    *,
    external_free_liabilities_e8: int,
    external_sp_custody_e8: int,
    core_free_debt_e8: int,
    core_sp_debt_e8: int,
    core_total_debt_e8: int,
) -> tuple[ZUSDGlobalDebtCoverViolation, ...]:
    violations: list[ZUSDGlobalDebtCoverViolation] = []
    if external_free_liabilities_e8 != core_free_debt_e8:
        violations.append(ZUSDGlobalDebtCoverViolation.FREE_DEBT_LIABILITY_MISMATCH)
    if external_sp_custody_e8 != core_sp_debt_e8:
        violations.append(ZUSDGlobalDebtCoverViolation.STABILITY_POOL_CUSTODY_MISMATCH)
    if _checked_add_u256(
        "core_debt_split_e8",
        core_free_debt_e8,
        core_sp_debt_e8,
    ) != core_total_debt_e8:
        violations.append(ZUSDGlobalDebtCoverViolation.CORE_DEBT_SPLIT_MISMATCH)
    if _checked_add_u256(
        "external_global_liabilities_e8",
        external_free_liabilities_e8,
        external_sp_custody_e8,
    ) != core_total_debt_e8:
        violations.append(ZUSDGlobalDebtCoverViolation.GLOBAL_DEBT_LIABILITY_MISMATCH)
    return tuple(violations)


@dataclass(frozen=True, slots=True)
class ZUSDGlobalDebtCoverDecision:
    violations: tuple[ZUSDGlobalDebtCoverViolation, ...]
    external_free_liabilities_e8: int
    external_sp_custody_e8: int
    core_free_debt_e8: int
    core_sp_debt_e8: int
    core_total_debt_e8: int

    def __post_init__(self) -> None:
        for field_name in (
            "external_free_liabilities_e8",
            "external_sp_custody_e8",
            "core_free_debt_e8",
            "core_sp_debt_e8",
            "core_total_debt_e8",
        ):
            _require_u256(field_name, getattr(self, field_name))
        if type(self.violations) is not tuple:
            raise TypeError("violations must be a tuple")
        if any(type(item) is not ZUSDGlobalDebtCoverViolation for item in self.violations):
            raise TypeError("violations must contain ZUSDGlobalDebtCoverViolation values")
        if tuple(item for item in _VIOLATION_ORDER if item in self.violations) != self.violations:
            raise ValueError("violations must be unique and canonically ordered")
        expected = _derive_violations(
            external_free_liabilities_e8=self.external_free_liabilities_e8,
            external_sp_custody_e8=self.external_sp_custody_e8,
            core_free_debt_e8=self.core_free_debt_e8,
            core_sp_debt_e8=self.core_sp_debt_e8,
            core_total_debt_e8=self.core_total_debt_e8,
        )
        if self.violations != expected:
            raise ValueError("global debt-cover decision is inconsistent")

    @property
    def covered(self) -> bool:
        return not self.violations

    @property
    def external_global_liabilities_e8(self) -> int:
        return _checked_add_u256(
            "external_global_liabilities_e8",
            self.external_free_liabilities_e8,
            self.external_sp_custody_e8,
        )


def evaluate_zusd_global_debt_cover(
    *,
    free_breakdown: ZUSDFreeDebtLiabilityBreakdown,
    stability_pool_escrow_e8: int,
    core_free_debt_e8: int,
    core_sp_debt_e8: int,
    core_total_debt_e8: int,
) -> ZUSDGlobalDebtCoverDecision:
    """Evaluate the complete scoped cover relation as a pure typed value."""

    if type(free_breakdown) is not ZUSDFreeDebtLiabilityBreakdown:
        raise TypeError("free_breakdown must be a ZUSDFreeDebtLiabilityBreakdown")
    external_free = free_breakdown.total_e8
    external_sp = _require_u256("stability_pool_escrow_e8", stability_pool_escrow_e8)
    core_free = _require_u256("core_free_debt_e8", core_free_debt_e8)
    core_sp = _require_u256("core_sp_debt_e8", core_sp_debt_e8)
    core_total = _require_u256("core_total_debt_e8", core_total_debt_e8)
    violations = _derive_violations(
        external_free_liabilities_e8=external_free,
        external_sp_custody_e8=external_sp,
        core_free_debt_e8=core_free,
        core_sp_debt_e8=core_sp,
        core_total_debt_e8=core_total,
    )
    return ZUSDGlobalDebtCoverDecision(
        violations=violations,
        external_free_liabilities_e8=external_free,
        external_sp_custody_e8=external_sp,
        core_free_debt_e8=core_free,
        core_sp_debt_e8=core_sp,
        core_total_debt_e8=core_total,
    )
