"""Pure zUSD owner-close E18-to-E8 quotient/residue projection.

This module implements only the F25 candidate arithmetic from the durable
owner-close contract. It produces no F15 composite certificate, performs no
physical transfer, and exposes no F16 committed post root.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

COLLATERAL_E18_TO_CUSTODY_E8_FACTOR = 10_000_000_000
MAX_U256 = (1 << 256) - 1


def _require_u256(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if value > MAX_U256:
        raise ValueError(f"{name} exceeds U256")
    return value


@dataclass(frozen=True, slots=True, order=True)
class CollateralE18Atoms:
    value: int

    def __post_init__(self) -> None:
        _require_u256("collateral_e18_atoms", self.value)


@dataclass(frozen=True, slots=True, order=True)
class CustodyE8Atoms:
    value: int

    def __post_init__(self) -> None:
        _require_u256("custody_e8_atoms", self.value)


@dataclass(frozen=True, slots=True, order=True)
class OwnerClaimE18Atoms:
    value: int

    def __post_init__(self) -> None:
        _require_u256("owner_claim_e18_atoms", self.value)


class OwnerCloseCustodyMode(str, Enum):
    BALANCED = "balanced"
    SURPLUS_QUARANTINED = "surplus_quarantined"
    DEFICIT_FROZEN = "deficit_frozen"


@dataclass(frozen=True, slots=True)
class OwnerCloseProjectionInput:
    closed_collateral_e18: CollateralE18Atoms
    active_pool_shadow_e18: CollateralE18Atoms
    accounted_custody_e8: CustodyE8Atoms
    observed_custody_e8: CustodyE8Atoms
    owner_external_e8: CustodyE8Atoms
    owner_claim_e18: OwnerClaimE18Atoms
    quarantine_e8: CustodyE8Atoms
    custody_mode: OwnerCloseCustodyMode

    def __post_init__(self) -> None:
        expected_types = (
            ("closed_collateral_e18", self.closed_collateral_e18, CollateralE18Atoms),
            ("active_pool_shadow_e18", self.active_pool_shadow_e18, CollateralE18Atoms),
            ("accounted_custody_e8", self.accounted_custody_e8, CustodyE8Atoms),
            ("observed_custody_e8", self.observed_custody_e8, CustodyE8Atoms),
            ("owner_external_e8", self.owner_external_e8, CustodyE8Atoms),
            ("owner_claim_e18", self.owner_claim_e18, OwnerClaimE18Atoms),
            ("quarantine_e8", self.quarantine_e8, CustodyE8Atoms),
        )
        for name, value, expected_type in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"{name} must be {expected_type.__name__}")
        if type(self.custody_mode) is not OwnerCloseCustodyMode:
            raise TypeError("custody_mode must be OwnerCloseCustodyMode")


class OwnerCloseProjectionViolation(str, Enum):
    DEFICIT_FROZEN = "deficit_frozen"
    ACTIVE_POOL_SHADOW_UNDERFLOW = "active_pool_shadow_underflow"
    ACCOUNTED_CUSTODY_UNDERFLOW = "accounted_custody_underflow"
    OBSERVED_CUSTODY_UNDERFLOW = "observed_custody_underflow"
    OWNER_EXTERNAL_OVERFLOW = "owner_external_overflow"
    OWNER_CLAIM_OVERFLOW = "owner_claim_overflow"


_VIOLATION_ORDER = (
    OwnerCloseProjectionViolation.DEFICIT_FROZEN,
    OwnerCloseProjectionViolation.ACTIVE_POOL_SHADOW_UNDERFLOW,
    OwnerCloseProjectionViolation.ACCOUNTED_CUSTODY_UNDERFLOW,
    OwnerCloseProjectionViolation.OBSERVED_CUSTODY_UNDERFLOW,
    OwnerCloseProjectionViolation.OWNER_EXTERNAL_OVERFLOW,
    OwnerCloseProjectionViolation.OWNER_CLAIM_OVERFLOW,
)


@dataclass(frozen=True, slots=True)
class NoPhysicalTransfer:
    """The physical quotient is zero; an adapter call is forbidden."""


@dataclass(frozen=True, slots=True)
class PhysicalTransferE8:
    amount: CustodyE8Atoms

    def __post_init__(self) -> None:
        if type(self.amount) is not CustodyE8Atoms:
            raise TypeError("amount must be CustodyE8Atoms")
        if self.amount.value == 0:
            raise ValueError("physical transfer amount must be positive")


OwnerClosePhysicalDirective = NoPhysicalTransfer | PhysicalTransferE8


def _split_xqr(closed_collateral_e18: int) -> tuple[int, int]:
    return divmod(closed_collateral_e18, COLLATERAL_E18_TO_CUSTODY_E8_FACTOR)


def _derive_arithmetic_violations(
    projection_input: OwnerCloseProjectionInput,
    *,
    quotient_e8: int,
    residue_e18: int,
) -> tuple[OwnerCloseProjectionViolation, ...]:
    violations: list[OwnerCloseProjectionViolation] = []
    if projection_input.closed_collateral_e18.value > projection_input.active_pool_shadow_e18.value:
        violations.append(OwnerCloseProjectionViolation.ACTIVE_POOL_SHADOW_UNDERFLOW)
    if quotient_e8 > projection_input.accounted_custody_e8.value:
        violations.append(OwnerCloseProjectionViolation.ACCOUNTED_CUSTODY_UNDERFLOW)
    if quotient_e8 > projection_input.observed_custody_e8.value:
        violations.append(OwnerCloseProjectionViolation.OBSERVED_CUSTODY_UNDERFLOW)
    if projection_input.owner_external_e8.value > MAX_U256 - quotient_e8:
        violations.append(OwnerCloseProjectionViolation.OWNER_EXTERNAL_OVERFLOW)
    if projection_input.owner_claim_e18.value > MAX_U256 - residue_e18:
        violations.append(OwnerCloseProjectionViolation.OWNER_CLAIM_OVERFLOW)
    return tuple(violations)


@dataclass(frozen=True, slots=True)
class OwnerCloseProjectionReject:
    violations: tuple[OwnerCloseProjectionViolation, ...]
    closed_collateral_e18: CollateralE18Atoms
    physical_quotient_e8: CustodyE8Atoms
    exact_residue_e18: OwnerClaimE18Atoms

    def __post_init__(self) -> None:
        if type(self.violations) is not tuple or not self.violations:
            raise TypeError("violations must be a non-empty tuple")
        if any(type(item) is not OwnerCloseProjectionViolation for item in self.violations):
            raise TypeError("violations must contain OwnerCloseProjectionViolation values")
        canonical = tuple(item for item in _VIOLATION_ORDER if item in self.violations)
        if canonical != self.violations:
            raise ValueError("violations must be unique and canonically ordered")
        if type(self.closed_collateral_e18) is not CollateralE18Atoms:
            raise TypeError("closed_collateral_e18 must be CollateralE18Atoms")
        if type(self.physical_quotient_e8) is not CustodyE8Atoms:
            raise TypeError("physical_quotient_e8 must be CustodyE8Atoms")
        if type(self.exact_residue_e18) is not OwnerClaimE18Atoms:
            raise TypeError("exact_residue_e18 must be OwnerClaimE18Atoms")
        quotient, residue = _split_xqr(self.closed_collateral_e18.value)
        if self.physical_quotient_e8.value != quotient or self.exact_residue_e18.value != residue:
            raise ValueError("rejected projection x/q/r values are inconsistent")

    @property
    def primary_violation(self) -> OwnerCloseProjectionViolation:
        return self.violations[0]


@dataclass(frozen=True, slots=True)
class OwnerCloseProjectionCandidate:
    closed_collateral_e18: CollateralE18Atoms
    physical_quotient_e8: CustodyE8Atoms
    exact_residue_e18: OwnerClaimE18Atoms
    active_pool_shadow_before_e18: CollateralE18Atoms
    active_pool_shadow_after_e18: CollateralE18Atoms
    accounted_custody_before_e8: CustodyE8Atoms
    accounted_custody_after_e8: CustodyE8Atoms
    observed_custody_before_e8: CustodyE8Atoms
    observed_custody_after_e8: CustodyE8Atoms
    owner_external_before_e8: CustodyE8Atoms
    owner_external_after_e8: CustodyE8Atoms
    owner_claim_before_e18: OwnerClaimE18Atoms
    owner_claim_after_e18: OwnerClaimE18Atoms
    quarantine_before_e8: CustodyE8Atoms
    quarantine_after_e8: CustodyE8Atoms
    physical_directive: OwnerClosePhysicalDirective

    def __post_init__(self) -> None:
        nominal_fields = (
            ("closed_collateral_e18", self.closed_collateral_e18, CollateralE18Atoms),
            ("physical_quotient_e8", self.physical_quotient_e8, CustodyE8Atoms),
            ("exact_residue_e18", self.exact_residue_e18, OwnerClaimE18Atoms),
            ("active_pool_shadow_before_e18", self.active_pool_shadow_before_e18, CollateralE18Atoms),
            ("active_pool_shadow_after_e18", self.active_pool_shadow_after_e18, CollateralE18Atoms),
            ("accounted_custody_before_e8", self.accounted_custody_before_e8, CustodyE8Atoms),
            ("accounted_custody_after_e8", self.accounted_custody_after_e8, CustodyE8Atoms),
            ("observed_custody_before_e8", self.observed_custody_before_e8, CustodyE8Atoms),
            ("observed_custody_after_e8", self.observed_custody_after_e8, CustodyE8Atoms),
            ("owner_external_before_e8", self.owner_external_before_e8, CustodyE8Atoms),
            ("owner_external_after_e8", self.owner_external_after_e8, CustodyE8Atoms),
            ("owner_claim_before_e18", self.owner_claim_before_e18, OwnerClaimE18Atoms),
            ("owner_claim_after_e18", self.owner_claim_after_e18, OwnerClaimE18Atoms),
            ("quarantine_before_e8", self.quarantine_before_e8, CustodyE8Atoms),
            ("quarantine_after_e8", self.quarantine_after_e8, CustodyE8Atoms),
        )
        for name, value, expected_type in nominal_fields:
            if type(value) is not expected_type:
                raise TypeError(f"{name} must be {expected_type.__name__}")
        if type(self.physical_directive) not in (NoPhysicalTransfer, PhysicalTransferE8):
            raise TypeError("physical_directive has an invalid variant")

        quotient, residue = _split_xqr(self.closed_collateral_e18.value)
        if self.physical_quotient_e8.value != quotient:
            raise ValueError("physical quotient is inconsistent")
        if self.exact_residue_e18.value != residue:
            raise ValueError("exact residue is inconsistent")
        if self.closed_collateral_e18.value != (
            COLLATERAL_E18_TO_CUSTODY_E8_FACTOR * quotient + residue
        ):
            raise ValueError("x/q/r decomposition is inconsistent")
        if residue >= COLLATERAL_E18_TO_CUSTODY_E8_FACTOR:
            raise ValueError("exact residue exceeds conversion factor")

        expected_values = (
            (
                self.active_pool_shadow_after_e18.value,
                self.active_pool_shadow_before_e18.value - self.closed_collateral_e18.value,
                "active-pool shadow successor is inconsistent",
            ),
            (
                self.accounted_custody_after_e8.value,
                self.accounted_custody_before_e8.value - quotient,
                "accounted-custody successor is inconsistent",
            ),
            (
                self.observed_custody_after_e8.value,
                self.observed_custody_before_e8.value - quotient,
                "observed-custody successor is inconsistent",
            ),
            (
                self.owner_external_after_e8.value,
                self.owner_external_before_e8.value + quotient,
                "owner-external successor is inconsistent",
            ),
            (
                self.owner_claim_after_e18.value,
                self.owner_claim_before_e18.value + residue,
                "owner-claim successor is inconsistent",
            ),
            (
                self.quarantine_after_e8.value,
                self.quarantine_before_e8.value,
                "quarantine successor is inconsistent",
            ),
        )
        for actual, expected, message in expected_values:
            if actual != expected:
                raise ValueError(message)

        if quotient == 0:
            if type(self.physical_directive) is not NoPhysicalTransfer:
                raise ValueError("zero quotient requires NoPhysicalTransfer")
        else:
            if type(self.physical_directive) is not PhysicalTransferE8:
                raise ValueError("positive quotient requires PhysicalTransferE8")
            if self.physical_directive.amount.value != quotient:
                raise ValueError("physical transfer amount is inconsistent")

    @property
    def is_commit_receipt(self) -> bool:
        return False


OwnerCloseProjectionOutcome = OwnerCloseProjectionCandidate | OwnerCloseProjectionReject


def project_owner_close_xqr(
    projection_input: OwnerCloseProjectionInput,
) -> OwnerCloseProjectionOutcome:
    """Project a non-authoritative F25 owner-close successor candidate."""

    if type(projection_input) is not OwnerCloseProjectionInput:
        raise TypeError("projection_input must be OwnerCloseProjectionInput")

    quotient, residue = _split_xqr(projection_input.closed_collateral_e18.value)
    quotient_value = CustodyE8Atoms(quotient)
    residue_value = OwnerClaimE18Atoms(residue)

    if projection_input.custody_mode is OwnerCloseCustodyMode.DEFICIT_FROZEN:
        return OwnerCloseProjectionReject(
            violations=(OwnerCloseProjectionViolation.DEFICIT_FROZEN,),
            closed_collateral_e18=projection_input.closed_collateral_e18,
            physical_quotient_e8=quotient_value,
            exact_residue_e18=residue_value,
        )

    violations = _derive_arithmetic_violations(
        projection_input,
        quotient_e8=quotient,
        residue_e18=residue,
    )
    if violations:
        return OwnerCloseProjectionReject(
            violations=violations,
            closed_collateral_e18=projection_input.closed_collateral_e18,
            physical_quotient_e8=quotient_value,
            exact_residue_e18=residue_value,
        )

    directive: OwnerClosePhysicalDirective
    if quotient == 0:
        directive = NoPhysicalTransfer()
    else:
        directive = PhysicalTransferE8(amount=quotient_value)

    return OwnerCloseProjectionCandidate(
        closed_collateral_e18=projection_input.closed_collateral_e18,
        physical_quotient_e8=quotient_value,
        exact_residue_e18=residue_value,
        active_pool_shadow_before_e18=projection_input.active_pool_shadow_e18,
        active_pool_shadow_after_e18=CollateralE18Atoms(
            projection_input.active_pool_shadow_e18.value
            - projection_input.closed_collateral_e18.value
        ),
        accounted_custody_before_e8=projection_input.accounted_custody_e8,
        accounted_custody_after_e8=CustodyE8Atoms(
            projection_input.accounted_custody_e8.value - quotient
        ),
        observed_custody_before_e8=projection_input.observed_custody_e8,
        observed_custody_after_e8=CustodyE8Atoms(
            projection_input.observed_custody_e8.value - quotient
        ),
        owner_external_before_e8=projection_input.owner_external_e8,
        owner_external_after_e8=CustodyE8Atoms(
            projection_input.owner_external_e8.value + quotient
        ),
        owner_claim_before_e18=projection_input.owner_claim_e18,
        owner_claim_after_e18=OwnerClaimE18Atoms(
            projection_input.owner_claim_e18.value + residue
        ),
        quarantine_before_e8=projection_input.quarantine_e8,
        quarantine_after_e8=projection_input.quarantine_e8,
        physical_directive=directive,
    )
