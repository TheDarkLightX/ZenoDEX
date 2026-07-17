"""Pure Liquity V1 liquidation offset/redistribution partition.

This module owns one arithmetic law only.  It does not decide liquidation
eligibility, select a vault, update Stability Pool accumulators, distribute
Default Pool rewards, or authorize ledger effects.  A composition kernel must
bind those decisions and commit their exact effects atomically before this
projection can participate in a mounted zUSD transition.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

LIQUITY_V1_MINIMUM_PROFILE = "zenodex/zusd-liquity-v1-minimum"
LIQUITY_V1_PARTITION_FORMULA = (
    "liquity/dev@8f52f2906f99414c0b1c3a84c95c74c319b7a8c6:"
    "TroveManager._getOffsetAndRedistributionVals"
)

MAX_U256 = (1 << 256) - 1
MAX_U512 = (1 << 512) - 1


def _require_u256(value: object, *, name: str, positive: bool = False) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    minimum = 1 if positive else 0
    if value < minimum:
        qualifier = "positive" if positive else "non-negative"
        raise ValueError(f"{name} must be {qualifier}")
    if value > MAX_U256:
        raise ValueError(f"{name} exceeds U256")
    return value


class ZUSDLiquidationPartitionBranch(str, Enum):
    """Exhaustive ordinary Liquity V1 offset branches."""

    FULL_REDISTRIBUTION = "full_redistribution"
    PARTIAL_OFFSET_AND_REDISTRIBUTION = "partial_offset_and_redistribution"
    FULL_OFFSET = "full_offset"


@dataclass(frozen=True)
class ZUSDLiquidationPartitionInput:
    """Validated exact-source inputs after keeper collateral compensation."""

    liquidated_debt_source: int
    post_keeper_comp_collateral_source: int
    stability_pool_principal_source: int

    def __post_init__(self) -> None:
        _require_u256(
            self.liquidated_debt_source,
            name="liquidated_debt_source",
            positive=True,
        )
        _require_u256(
            self.post_keeper_comp_collateral_source,
            name="post_keeper_comp_collateral_source",
        )
        _require_u256(
            self.stability_pool_principal_source,
            name="stability_pool_principal_source",
        )


@dataclass(frozen=True)
class ZUSDLiquidationPartitionPlan:
    """A complete and internally checked ordinary liquidation partition.

    The plan is an arithmetic candidate, not an authority receipt.  It carries
    no actor, target vault, pre-state root, oracle root, or effect-plan root and
    therefore cannot authorize a live transition by itself.
    """

    liquidated_debt_source: int
    post_keeper_comp_collateral_source: int
    stability_pool_principal_source: int
    debt_to_offset_source: int
    collateral_to_stability_pool_source: int
    debt_to_redistribute_source: int
    collateral_to_redistribute_source: int
    branch: ZUSDLiquidationPartitionBranch

    def __post_init__(self) -> None:
        debt = _require_u256(
            self.liquidated_debt_source,
            name="liquidated_debt_source",
            positive=True,
        )
        collateral = _require_u256(
            self.post_keeper_comp_collateral_source,
            name="post_keeper_comp_collateral_source",
        )
        principal = _require_u256(
            self.stability_pool_principal_source,
            name="stability_pool_principal_source",
        )
        offset = _require_u256(
            self.debt_to_offset_source,
            name="debt_to_offset_source",
        )
        collateral_to_pool = _require_u256(
            self.collateral_to_stability_pool_source,
            name="collateral_to_stability_pool_source",
        )
        debt_to_redistribute = _require_u256(
            self.debt_to_redistribute_source,
            name="debt_to_redistribute_source",
        )
        collateral_to_redistribute = _require_u256(
            self.collateral_to_redistribute_source,
            name="collateral_to_redistribute_source",
        )
        if type(self.branch) is not ZUSDLiquidationPartitionBranch:
            raise TypeError("branch must be a ZUSDLiquidationPartitionBranch")

        expected_offset = min(debt, principal)
        expected_collateral_to_pool = collateral * expected_offset // debt
        expected_branch = _branch_for(debt=debt, principal=principal)
        if offset != expected_offset:
            raise ValueError("debt offset does not equal min(debt, principal)")
        if collateral_to_pool != expected_collateral_to_pool:
            raise ValueError("Stability Pool collateral share is not exact floor")
        if offset + debt_to_redistribute != debt:
            raise ValueError("debt partition does not conserve")
        if collateral_to_pool + collateral_to_redistribute != collateral:
            raise ValueError("collateral partition does not conserve")
        if self.branch is not expected_branch:
            raise ValueError("branch does not match Stability Pool capacity")

    @property
    def profile_id(self) -> str:
        return LIQUITY_V1_MINIMUM_PROFILE

    @property
    def formula_version(self) -> str:
        return LIQUITY_V1_PARTITION_FORMULA

    def observable_values(self) -> tuple[tuple[str, int | str], ...]:
        """Return the canonical ESSO-compatible observable order."""

        return (
            ("debt_to_offset", self.debt_to_offset_source),
            (
                "collateral_to_sp",
                self.collateral_to_stability_pool_source,
            ),
            ("debt_to_redistribute", self.debt_to_redistribute_source),
            (
                "collateral_to_redistribute",
                self.collateral_to_redistribute_source,
            ),
            ("branch", _esso_branch(self.branch)),
        )


def _branch_for(
    *, debt: int, principal: int
) -> ZUSDLiquidationPartitionBranch:
    if principal == 0:
        return ZUSDLiquidationPartitionBranch.FULL_REDISTRIBUTION
    if principal < debt:
        return ZUSDLiquidationPartitionBranch.PARTIAL_OFFSET_AND_REDISTRIBUTION
    return ZUSDLiquidationPartitionBranch.FULL_OFFSET


def _esso_branch(branch: ZUSDLiquidationPartitionBranch) -> int:
    if branch is ZUSDLiquidationPartitionBranch.FULL_REDISTRIBUTION:
        return 0
    if branch is ZUSDLiquidationPartitionBranch.PARTIAL_OFFSET_AND_REDISTRIBUTION:
        return 1
    return 2


def compute_liquity_v1_liquidation_partition(
    inputs: ZUSDLiquidationPartitionInput,
) -> ZUSDLiquidationPartitionPlan:
    """Compute the source-pinned ordinary offset/redistribution partition."""

    if type(inputs) is not ZUSDLiquidationPartitionInput:
        raise TypeError("inputs must be a ZUSDLiquidationPartitionInput")
    debt = inputs.liquidated_debt_source
    collateral = inputs.post_keeper_comp_collateral_source
    principal = inputs.stability_pool_principal_source
    debt_to_offset = min(debt, principal)
    collateral_product = collateral * debt_to_offset
    if collateral_product > MAX_U512:
        raise ValueError("collateral offset product exceeds U512")
    collateral_to_pool = collateral_product // debt
    return ZUSDLiquidationPartitionPlan(
        liquidated_debt_source=debt,
        post_keeper_comp_collateral_source=collateral,
        stability_pool_principal_source=principal,
        debt_to_offset_source=debt_to_offset,
        collateral_to_stability_pool_source=collateral_to_pool,
        debt_to_redistribute_source=debt - debt_to_offset,
        collateral_to_redistribute_source=collateral - collateral_to_pool,
        branch=_branch_for(debt=debt, principal=principal),
    )
