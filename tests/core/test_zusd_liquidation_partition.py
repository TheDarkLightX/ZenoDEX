from __future__ import annotations

from dataclasses import replace

import pytest

from generated.liquity_v1_sp_offset_redistribution_bounded.python_ref import (
    liquity_v1_sp_offset_redistribution_bounded_ref as esso_reference,
)
from src.core.zusd_liquidation_partition import (
    LIQUITY_V1_MINIMUM_PROFILE,
    MAX_U256,
    ZUSDLiquidationPartitionBranch,
    ZUSDLiquidationPartitionInput,
    compute_liquity_v1_liquidation_partition,
)


def _compute(
    debt: int, collateral: int, principal: int
):
    return compute_liquity_v1_liquidation_partition(
        ZUSDLiquidationPartitionInput(
            liquidated_debt_source=debt,
            post_keeper_comp_collateral_source=collateral,
            stability_pool_principal_source=principal,
        )
    )


@pytest.mark.parametrize(
    ("debt", "collateral", "principal", "expected_branch"),
    (
        (4, 3, 0, ZUSDLiquidationPartitionBranch.FULL_REDISTRIBUTION),
        (
            4,
            3,
            2,
            ZUSDLiquidationPartitionBranch.PARTIAL_OFFSET_AND_REDISTRIBUTION,
        ),
        (4, 3, 4, ZUSDLiquidationPartitionBranch.FULL_OFFSET),
        (4, 3, MAX_U256, ZUSDLiquidationPartitionBranch.FULL_OFFSET),
    ),
)
def test_liquidation_partition_branch_is_total_and_capacity_exact(
    debt: int,
    collateral: int,
    principal: int,
    expected_branch: ZUSDLiquidationPartitionBranch,
) -> None:
    plan = _compute(debt, collateral, principal)

    assert plan.branch is expected_branch
    assert plan.debt_to_offset_source == min(debt, principal)
    assert (
        plan.debt_to_offset_source + plan.debt_to_redistribute_source == debt
    )
    assert (
        plan.collateral_to_stability_pool_source
        + plan.collateral_to_redistribute_source
        == collateral
    )
    assert plan.profile_id == LIQUITY_V1_MINIMUM_PROFILE


def test_liquidation_partition_matches_esso_on_full_bounded_domain() -> None:
    state = esso_reference.init_state()
    for debt in range(1, 5):
        for collateral in range(5):
            for principal in range(5):
                reference = esso_reference.step(
                    state,
                    esso_reference.Command(
                        tag="partition_offset_and_redistribution",
                        args={
                            "new_debt": debt,
                            "new_collateral": collateral,
                            "new_sp_deposits": principal,
                        },
                    ),
                )
                assert reference.ok is True, reference.error
                assert reference.effects is not None
                plan = _compute(debt, collateral, principal)
                assert dict(plan.observable_values()) == dict(reference.effects)
                assert reference.state is not None
                state = reference.state


@pytest.mark.parametrize(
    "field",
    (
        "liquidated_debt_source",
        "post_keeper_comp_collateral_source",
        "stability_pool_principal_source",
    ),
)
def test_liquidation_partition_rejects_boolean_integer_aliases(field: str) -> None:
    values: dict[str, object] = {
        "liquidated_debt_source": 1,
        "post_keeper_comp_collateral_source": 1,
        "stability_pool_principal_source": 1,
    }
    values[field] = True
    with pytest.raises(TypeError, match=f"{field} must be an int"):
        ZUSDLiquidationPartitionInput(**values)  # type: ignore[arg-type]


def test_liquidation_partition_rejects_zero_debt_and_u256_overflow() -> None:
    with pytest.raises(ValueError, match="liquidated_debt_source must be positive"):
        _compute(0, 1, 1)
    with pytest.raises(ValueError, match="exceeds U256"):
        _compute(1, MAX_U256 + 1, 1)


def test_liquidation_partition_plan_cannot_be_forged() -> None:
    plan = _compute(4, 3, 2)
    with pytest.raises(ValueError, match="debt partition does not conserve"):
        replace(plan, debt_to_redistribute_source=3)
    with pytest.raises(ValueError, match="collateral share is not exact floor"):
        replace(plan, collateral_to_stability_pool_source=2)
    with pytest.raises(ValueError, match="branch does not match"):
        replace(plan, branch=ZUSDLiquidationPartitionBranch.FULL_OFFSET)


def test_liquidation_partition_u256_boundary_uses_u512_product() -> None:
    plan = _compute(MAX_U256, MAX_U256, MAX_U256)

    assert plan.debt_to_offset_source == MAX_U256
    assert plan.collateral_to_stability_pool_source == MAX_U256
    assert plan.debt_to_redistribute_source == 0
    assert plan.collateral_to_redistribute_source == 0
    assert plan.branch is ZUSDLiquidationPartitionBranch.FULL_OFFSET


def test_liquidation_partition_rejects_untyped_input() -> None:
    with pytest.raises(
        TypeError,
        match="inputs must be a ZUSDLiquidationPartitionInput",
    ):
        compute_liquity_v1_liquidation_partition(object())  # type: ignore[arg-type]
